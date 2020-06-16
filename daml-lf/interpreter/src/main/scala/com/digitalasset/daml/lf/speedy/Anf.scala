// Copyright (c) 2020 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.daml.lf.speedy

/**
  * Transformation to ANF based AST for the speedy interpreter.
  */
import com.daml.lf.speedy.SExpr._

import scala.annotation.tailrec

object Anf {

  case class CompilationError(error: String) extends RuntimeException(error, null, true, false)

  case class DepthE(n: Int)
  case class DepthA(n: Int)

  case class Env(absMap: Map[DepthE, DepthA], oldDepth: DepthE)

  val initEnv = Env(absMap = Map.empty, oldDepth = DepthE(0))

  def trackBindings(depth: DepthA, env: Env, n: Int): Env = {
    if (n == 0) {
      env
    } else {
      val extra = (0 to n - 1).map(i => (DepthE(env.oldDepth.n + i), DepthA(depth.n + i)))
      Env(absMap = env.absMap ++ extra, oldDepth = DepthE(env.oldDepth.n + n))
    }
  }

  type Anf = SExpr

  sealed trait Trampoline[T] {
    @tailrec
    def bounce: T = this match {
      case Land(x) => x
      case Bounce(continue) => continue().bounce
    }
  }

  final case class Land[T](x: T) extends Trampoline[T]
  final case class Bounce[T](continue: () => Trampoline[T]) extends Trampoline[T]

  type Res = Trampoline[Anf]
  type K[T] = ((DepthA, T) => Res)

  case class AbsBinding(abs: DepthA)

  def makeAbsoluteB(env: Env, rel: Int): AbsBinding = {
    val oldAbs = DepthE(env.oldDepth.n - rel)
    env.absMap.get(oldAbs) match {
      case None => throw CompilationError(s"makeAbsoluteB(env=$env,rel=$rel)")
      case Some(abs) => AbsBinding(abs)
    }
  }

  def makeRelativeB(depth: DepthA, binding: AbsBinding): Int = {
    (depth.n - binding.abs.n)
  }

  type AbsAtom = Either[SExprAtomic, AbsBinding]

  def makeAbsoluteA(env: Env, atom: SExprAtomic): AbsAtom = atom match {
    case SELocS(rel) => Right(makeAbsoluteB(env, rel))
    case x: SELocA => Left(x)
    case x: SELocF => Left(x)
    case x: SEBuiltin => Left(x)
    case x: SEValue => Left(x)
  }

  def makeRelativeA(depth: DepthA)(atom: AbsAtom): SExprAtomic = atom match {
    case Left(x: SELocS) => throw CompilationError(s"makeRelativeA: unexpected: $x")
    case Left(atom) => atom
    case Right(binding) => SELocS(makeRelativeB(depth, binding))
  }

  def relocateA(depth: DepthA, env: Env)(atom: SExprAtomic): SExprAtomic = {
    makeRelativeA(depth)(makeAbsoluteA(env, atom))
  }

  // TODO: ? inline AbsLoc, makeAbsolute/Relative(L) -- all we need in relocateL
  type AbsLoc = Either[SELoc, AbsBinding]

  def makeAbsoluteL(env: Env, loc: SELoc): AbsLoc = loc match {
    case SELocS(rel) => Right(makeAbsoluteB(env, rel))
    case x: SELocA => Left(x)
    case x: SELocF => Left(x)
  }

  def makeRelativeL(depth: DepthA)(loc: AbsLoc): SELoc = loc match {
    case Left(x: SELocS) => throw CompilationError(s"makeRelativeL: unexpected: $x")
    case Left(loc) => loc
    case Right(binding) => SELocS(makeRelativeB(depth, binding))
  }

  def relocateL(depth: DepthA, env: Env)(loc: SELoc): SELoc = {
    makeRelativeL(depth)(makeAbsoluteL(env, loc))
  }

  // flatten* -- non-continuation entry points

  def flattenEntry(exp: SExpr): Anf = {
    val depth = DepthA(0)
    val env = initEnv
    flattenExp(depth, env, exp)
  }

  def flattenExp(depth: DepthA, env: Env, exp: SExpr): Anf = {
    val k0: K[Anf] = {
      case (depth @ _, anf) => Land(anf)
    }
    transformExp(depth, env, exp, k0).bounce
  }

  // transform* -- continuation entry points

  def transformLet1(depth: DepthA, env: Env, rhs: SExpr, body: SExpr, k: K[SExpr]): Res = {
    val rhs1 = flattenExp(depth, env, rhs)
    val depth1 = DepthA(depth.n + 1)
    val env1 = trackBindings(depth, env, 1)
    val body1 = flattenExp(depth1, env1, body)
    k(depth, SELet1(rhs1, body1))
  }

  /*def transformLet1(depth: DepthA, env: Env, rhs: SExpr, body: SExpr, k: K[SExpr]): Res = {
    // This is a better transform, but sadly it can blow the stack for deeply nested lets.
    transformExp(depth, env, rhs, {
      case (depth, rhs) =>
        val depth1 = DepthA(depth.n + 1)
        val env1 = trackBindings(depth, env, 1)
        val body1 = transformExp(depth1, env1, body, k).bounce
        Land(SELet1(rhs, body1))
    })
  }*/

  //TODO: inline
  def flattenAlts(depth: DepthA, env: Env, alts: Array[SCaseAlt]): Array[SCaseAlt] = {
    alts.map {
      case SCaseAlt(pat, body0) =>
        val n = patternNArgs(pat)
        val env1 = trackBindings(depth, env, n)
        val body = flattenExp(DepthA(depth.n + n), env1, body0)
        SCaseAlt(pat, body)
    }
  }

  def patternNArgs(pat: SCasePat): Int = pat match {
    case _: SCPEnum | _: SCPPrimCon | SCPNil | SCPDefault | SCPNone => 0
    case _: SCPVariant | SCPSome => 1
    case SCPCons => 2
  }

  def transformExp(depth: DepthA, env: Env, exp: SExpr, k: K[SExpr]): Res =
    Bounce(() =>
      exp match {
        case atom: SExprAtomic => k(depth, relocateA(depth, env)(atom))
        case x: SEVal => k(depth, x)
        case x: SEBuiltinRecursiveDefinition => k(depth, x)

        case SEAppGeneral(func, args) =>
          atomizeExp(
            depth,
            env,
            func, {
              case (depth, func) =>
                atomizeExps(
                  depth,
                  env,
                  args.toList, {
                    case (depth, args) =>
                      val func1 = makeRelativeA(depth)(func)
                      val args1 = args.map(makeRelativeA(depth))
                      k(depth, SEAppAtomic(func1, args1.toArray))
                  }
                )
            }
          )
        case SEMakeClo(fvs0, arity, body0) =>
          val fvs = fvs0.map(relocateL(depth, env))
          val body = flattenEntry(body0)
          k(depth, SEMakeClo(fvs, arity, body))

        case SECase(scrut, alts0) =>
          transformExp(depth, env, scrut, {
            case (depth, scrut) =>
              //val scrut1 = makeRelativeA(depth)(scrut)
              val alts = flattenAlts(depth, env, alts0)
              k(depth, SECase(scrut, alts))
          })

        case SELet(rhss, body) =>
          val expanded = expandMultiLet(rhss.toList, body)
          transformExp(depth, env, expanded, k)

        case SELet1General(rhs, body) =>
          transformLet1(depth, env, rhs, body, k)

        case SECatch(body0, handler0, fin0) =>
          val body = flattenExp(depth, env, body0)
          val handler = flattenExp(depth, env, handler0)
          val fin = flattenExp(depth, env, fin0)
          k(depth, SECatch(body, handler, fin))

        case SELocation(loc, body) =>
          transformExp(depth, env, body, {
            case (depth, body) =>
              //val body1 = makeRelativeA(depth)(body)
              k(depth, SELocation(loc, body))
          })

        case SELabelClosure(label, exp) =>
          transformExp(depth, env, exp, {
            case (depth, exp) =>
              k(depth, SELabelClosure(label, exp))
          })

        case x: SEAbs => throw CompilationError(s"flatten: unexpected: $x")
        case x: SEWronglyTypeContractId => throw CompilationError(s"flatten: unexpected: $x")
        case x: SEImportValue => throw CompilationError(s"flatten: unexpected: $x")
        case x: SEVar => throw CompilationError(s"flatten: unexpected: $x")

        case x: SEAppAtomicGeneral => throw CompilationError(s"flatten: unexpected: $x")
        case x: SEAppAtomicSaturatedBuiltin => throw CompilationError(s"flatten: unexpected: $x")
        //case x: SELet1General => throw CompilationError(s"flatten: unexpected: $x")
        case x: SELet1Builtin => throw CompilationError(s"flatten: unexpected: $x")

    })

  def atomizeExps(depth: DepthA, env: Env, exps: List[SExpr], k: K[List[AbsAtom]]): Res =
    exps match {
      case Nil => k(depth, Nil)
      case exp :: exps =>
        Bounce(() =>
          atomizeExp(depth, env, exp, {
            case (depth, atom) =>
              atomizeExps(depth, env, exps, {
                case (depth, atoms) =>
                  Bounce(() => k(depth, atom :: atoms))
              })
          }))
    }

  def atomizeExp(depth: DepthA, env: Env, exp: SExpr, k: K[AbsAtom]): Res = {
    exp match {
      case ea: SExprAtomic => k(depth, makeAbsoluteA(env, ea))
      case _ =>
        transformExp(depth, env, exp, {
          case (depth, anf) =>
            val atom = Right(AbsBinding(depth))
            val body = k(DepthA(depth.n + 1), atom).bounce
            Land(SELet1(anf, body))
        })
    }
  }

  def expandMultiLet(rhss: List[SExpr], body: SExpr): SExpr = {
    //loop over rhss in reverse order
    @tailrec
    def loop(acc: SExpr, xs: List[SExpr]): SExpr = {
      xs match {
        case Nil => acc
        case rhs :: xs => loop(SELet1General(rhs, acc), xs)
      }
    }
    loop(body, rhss.reverse)
  }

}
