// Copyright (c) 2020 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.daml.extractor.helpers

import java.time.Instant
import java.util.concurrent.TimeUnit

import com.daml.ledger.api.v1.commands.{Command, CreateCommand, ExerciseCommand}
import com.daml.ledger.api.v1.value.Value.Sum.{
  Numeric,
  Int64,
  Party,
  Text,
  Timestamp,
  List => DamlListValue
}
import com.daml.ledger.api.v1.value.{Identifier, Record, RecordField, Value, List => DamlList}

import scala.language.implicitConversions

object ValueConversions {

  implicit class StringValues(val s: String) extends AnyVal {
    def asParty: Value = Value(Party(s))
    def asNumeric: Value = Value(Numeric(s))
    def asText: Value = Value(Text(s))
  }

  implicit class InstantValues(val i: Instant) extends AnyVal {
    def asTime: Value = {
      val micros = TimeUnit.SECONDS.toMicros(i.getEpochSecond) + TimeUnit.NANOSECONDS.toMicros(
        i.getNano.toLong)
      Value(Timestamp(micros))
    }
  }

  implicit class LongValues(val i: Long) extends AnyVal {
    def asInt64: Value = Value(Int64(i))
  }

  implicit class LabeledValues(val labeledValues: Seq[(String, Value)]) extends AnyVal {
    def asRecord = Record(None, recordFields)

    def asRecordOf(identifier: Identifier) = Record(Some(identifier), recordFields)

    def asRecordValue = Value(Value.Sum.Record(asRecord))

    def asRecordValueOf(identifier: Identifier) = Value(Value.Sum.Record(asRecordOf(identifier)))

    private def recordFields: Seq[RecordField] = {
      labeledValues.map {
        case (k, v) => RecordField(k, Some(v))
      }
    }
  }

  implicit class ValueSequences(val values: Seq[Value]) extends AnyVal {
    def asList = Value(DamlListValue(DamlList(values)))
  }

  implicit def value2Optional(value: Value): Option[Value] = Some(value)

  implicit class ExerciseCommands(val exercise: ExerciseCommand) extends AnyVal {
    def wrap = Command(Command.Command.Exercise(exercise))
  }

  implicit class CreateCommands(val create: CreateCommand) extends AnyVal {
    def wrap = Command(Command.Command.Create(create))
  }

}
