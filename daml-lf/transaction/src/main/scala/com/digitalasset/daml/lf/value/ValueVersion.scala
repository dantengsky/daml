// Copyright (c) 2020 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.daml.lf
package value

import com.daml.lf.value.Value._
import com.daml.lf.data.{Decimal, FrontStack, FrontStackCons, ImmArray}
import com.daml.lf.transaction.VersionTimeline

import scala.annotation.tailrec

final case class ValueVersion(protoValue: String)

/**
  * Currently supported versions of the DAML-LF value specification.
  */
object ValueVersions
    extends LfVersions(versionsAscending = VersionTimeline.ascendingVersions[ValueVersion])(
      _.protoValue,
    ) {

  private[value] val minVersion = ValueVersion("1")
  private[value] val minOptional = ValueVersion("2")
  private[value] val minContractIdStruct = ValueVersion("3")
  private[value] val minMap = ValueVersion("4")
  private[value] val minEnum = ValueVersion("5")
  private[value] val minNumeric = ValueVersion("6")
  private[value] val minGenMap = ValueVersion("7")
  private[value] val minContractIdV1 = ValueVersion("7")

  // Older versions are deprecated https://github.com/digital-asset/daml/issues/5220
  // We force output of recent version, but keep reading older version as long as
  // Sandbox is alive.
  val DefaultSupportedVersions = VersionRange(ValueVersion("6"), acceptedVersions.last)

  def assignVersion[Cid](
      v0: Value[Cid],
      supportedVersions: VersionRange[ValueVersion] = DefaultSupportedVersions,
  ): Either[String, ValueVersion] =
    assignVersion(v0, supportedVersions.min, supportedVersions.max)

  def assignVersion[Cid](
      v0: Value[Cid],
      minVersion: ValueVersion,
      maxVersion: ValueVersion,
  ): Either[String, ValueVersion] = {
    import VersionTimeline.{maxVersion => maxVV}
    import VersionTimeline.Implicits._

    @tailrec
    def go(
        currentVersion: ValueVersion,
        values0: FrontStack[Value[Cid]],
    ): Either[String, ValueVersion] = {
      if (currentVersion == maxVersion) {
        Right(currentVersion)
      } else {
        values0 match {
          case FrontStack() => Right(currentVersion)
          case FrontStackCons(value, values) =>
            value match {
              // for things supported since version 1, we do not need to check
              case ValueRecord(_, fs) => go(currentVersion, fs.map(v => v._2) ++: values)
              case ValueVariant(_, _, arg) => go(currentVersion, arg +: values)
              case ValueList(vs) => go(currentVersion, vs.toImmArray ++: values)
              case ValueContractId(_) | ValueInt64(_) | ValueText(_) | ValueTimestamp(_) |
                  ValueParty(_) | ValueBool(_) | ValueDate(_) | ValueUnit =>
                go(currentVersion, values)
              case ValueNumeric(x) if x.scale == Decimal.scale =>
                go(currentVersion, values)
              // for things added after version 1, we raise the minimum if present
              case ValueNumeric(_) =>
                go(maxVV(minNumeric, currentVersion), values)
              case ValueOptional(x) =>
                go(maxVV(minOptional, currentVersion), ImmArray(x.toList) ++: values)
              case ValueTextMap(map) =>
                go(maxVV(minMap, currentVersion), map.values ++: values)
              case ValueGenMap(entries) =>
                val newValues = entries.iterator.foldLeft(values) {
                  case (acc, (key, value)) => key +: value +: acc
                }
                go(maxVV(minGenMap, currentVersion), newValues)
              case ValueEnum(_, _) =>
                go(maxVV(minEnum, currentVersion), values)
              // structs are a no-no
              case ValueStruct(fields) =>
                Left(s"Got struct when trying to assign version. Fields: $fields")
            }
        }
      }
    }

    go(minVersion, FrontStack(v0)) match {
      case Right(inferredVersion) if maxVersion precedes inferredVersion =>
        Left(s"inferred version $inferredVersion is not supported")
      case res =>
        res
    }

  }

  @throws[IllegalArgumentException]
  def assertAssignVersion[Cid](
      v0: Value[Cid],
      supportedVersions: VersionRange[ValueVersion] = DefaultSupportedVersions,
  ): ValueVersion =
    data.assertRight(assignVersion(v0, supportedVersions))

  def asVersionedValue[Cid](
      value: Value[Cid],
      supportedVersions: VersionRange[ValueVersion] = DefaultSupportedVersions,
  ): Either[String, VersionedValue[Cid]] =
    assignVersion(value, supportedVersions).map(VersionedValue(_, value))

  @throws[IllegalArgumentException]
  def assertAsVersionedValue[Cid](
      value: Value[Cid],
      supportedVersions: VersionRange[ValueVersion] = DefaultSupportedVersions,
  ): VersionedValue[Cid] =
    data.assertRight(asVersionedValue(value, supportedVersions))
}
