// Copyright (c) 2020 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.daml.lf.engine.trigger.dao

import java.util.UUID

import com.daml.lf.engine.trigger.{RunningTrigger, UserCredentials}

trait RunningTriggerDao {
  def addRunningTrigger(t: RunningTrigger): Either[String, Unit]
  def removeRunningTrigger(triggerInstance: UUID): Either[String, Boolean]
  def listRunningTriggers(credentials: UserCredentials): Either[String, Vector[UUID]]
}
