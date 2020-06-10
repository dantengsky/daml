// Copyright (c) 2020 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.daml.lf.speedy

/**
  * ANF based AST for the speedy interpreter.
  */
import com.daml.lf.speedy.SExpr._

object Anf {

  case class CompilationError(error: String) extends RuntimeException(error, null, true, false)

  case class Env(absMap: Map[Int, Int], newDepth: Int)

  val initEnv = Env(absMap = Map.empty, newDepth = 0)

  def remapRelStackOffset(oldDepth: Int, env: Env, oldRel: Int): Int = {
    val oldAbs = oldDepth - oldRel
    env match {
      case Env(absMap,newDepth) =>
        absMap.get(oldAbs) match {
          case None =>
            throw CompilationError(s"remapStackLocation(oldDepth=$oldDepth,env=$env,oldRel=$oldRel,oldAbs=$oldAbs)")
          case Some(newAbs) =>
            val newRel = newDepth - newAbs
            //println(s"remapStackLocation(oldDepth=$oldDepth,env=$env,oldRel=$oldRel -> oldAbs=$oldAbs -> newAbs=$newAbs -> newRel=$newRel")
            newRel
        }
    }
  }

  def trackBindings(oldDepth: Int, env: Env, n: Int) : Env = {
    if (n == 0) {
      env
    } else {
      env match {
        case Env(absMap,newDepth) =>
          val extra = (0 to n-1).map(i => (oldDepth + i, newDepth + i))
          val newEnv = Env(absMap ++ extra,newDepth + n)
          //println(s"trackBindings(oldDepth=$oldDepth,env=$env,n=$n) -> newEnv=$newEnv")
          newEnv
      }
    }
  }

  case class NewBinding(madeAtDepth: Int)

  def makeNewBinding(env: Env) : (Env,NewBinding) = {
    env match {
      case Env(absMap,newDepth) =>
        val res = (Env(absMap,newDepth + 1), NewBinding(madeAtDepth = newDepth))
        res
    }
  }

  type Atom = Either[SExprAtomic,NewBinding]


  type Res = SExpr
  type K[T] = ((Env, T) => Res)


  // TODO: inline?
  def relocateExpAtomic(depth: Int, env: Env, exp: SExprAtomic): SExprAtomic = exp match {
    case SELocS(n) => SELocS (remapRelStackOffset(depth, env, n))
    case atomic => atomic
  }

  def relocateAtom(depth: Int, env: Env)(atom: Atom) : SExprAtomic = {
    val exp =
      atom match {
        case Left(exp) => relocateExpAtomic(depth,env,exp)
        case Right(NewBinding(madeAtDepth)) =>
          val rel: Int = env.newDepth - madeAtDepth
        SELocS(rel)
      }
    //println(s"expandAtom(madeAtDepth=$madeAtDepth), env.newDepth=${env.newDepth} -> rel=$rel")
    //println(s"relocateAtom: $atom -> $exp")
    exp
  }

  // flatten* -- non-continuation entry points

  def flattenEntry(exp: SExpr): SExpr = {
    val depth = 0
    val env = initEnv
    flattenExp(depth,env,exp)
  }

  def flattenExp(depth: Int, env: Env, exp: SExpr): SExpr = {
    atomizeExp(depth, env, exp, { case (env,atom) =>
      relocateAtom(depth,env)(atom)
    })
  }

  // transform* -- continuation entry points

  //TODO: inline?
  def transformLets(depth: Int, env: Env, rhss: List[SExpr], body: SExpr, k: K[SExpr]): Res = rhss match {
    case rhs::rhss =>
      atomizeExp(depth, env, rhs, { case (env,rhs) =>
        val rhs1 = relocateAtom(depth,env)(rhs)
        SELet(Array(rhs1),
          transformLets(depth + 1, trackBindings(depth,env,1), rhss, body, k))
      })
    case Nil =>
      transformExp(depth,env,body, { case (env,exp) =>
        k(env,exp)
      })
  }

  //TODO: inline
  def remapLocation(depth: Int, env: Env)(loc: SELoc): SELoc = loc match {
    case SELocS(n) => SELocS(remapRelStackOffset(depth, env, n))
    case SELocA(_) | SELocF(_) => loc
  }

  //TODO: inline
  def flattenAlts(depth: Int, env: Env, alts: Array[SCaseAlt]): Array[SCaseAlt] = {
    alts.map{ case SCaseAlt(pat,body0) =>
      val n = patternNArgs(pat)
      val body = flattenExp(depth + n, trackBindings(depth, env, n), body0)
      SCaseAlt(pat,body)
    }
  }

  def patternNArgs(pat: SCasePat): Int = pat match {
    case _: SCPEnum | _: SCPPrimCon | SCPNil | SCPDefault | SCPNone => 0
    case _: SCPVariant | SCPSome => 1
    case SCPCons => 2
  }


  def transformExp(depth: Int, env: Env, exp: SExpr, k: K[SExpr]): Res = exp match {

    case x: SExprAtomic => k (env,x)
    case x: SEVal => k(env, x)
    case x: SEBuiltinRecursiveDefinition => k(env, x)

    case SEAppGeneral(func, args) =>
      atomizeExp(depth, env, func, { case (env, func) =>
        atomizeExps(depth, env, args.toList, { case (env, args) =>
          val func1 = relocateAtom(depth,env)(func)
          val args1 = args.map(relocateAtom(depth,env)).toArray
          k(env, SEAppAtomic(func1, args1))
        })
      })

    case x: SEAppAtomic =>
      throw CompilationError(s"flatten: unexpected: $x")

    case SEMakeClo(fvs0, arity, body0) =>
      val fvs = fvs0.map(remapLocation(depth,env))
      val body = flattenEntry(body0)
      k(env, SEMakeClo(fvs, arity, body))

    case SECase(scrut, alts0) =>
      atomizeExp(depth, env, scrut, { case (env, scrut) =>
        val scrut1 = relocateAtom(depth,env)(scrut)
        val alts = flattenAlts(depth, env, alts0)
        k(env, SECase(scrut1, alts))
      })

    case SELet(rhss, body) =>
      transformLets(depth, env, rhss.toList, body, k)

    case SECatch(body, handler0, fin0) => // handler & fin are always just True/False
      atomizeExp(depth, env, body, { case (env, body) =>
        val body1 = relocateAtom(depth,env)(body)
        val handler = flattenExp(depth,env,handler0)
        val fin = flattenExp(depth,env,fin0)
        k(env, SECatch(body1, handler, fin))
      })

    case SELocation(loc, body) =>
      atomizeExp(depth, env, body, { case (env, body) =>
        val body1 = relocateAtom(depth,env)(body)
        k(env, SELocation(loc, body1))
      })

    case SELabelClosure(label, exp) =>
      atomizeExp(depth, env, exp, { case (env, exp) =>
        val exp1 = relocateAtom(depth,env)(exp)
        k(env, SELabelClosure(label, exp1))
      })

    case x: SEAbs => throw CompilationError(s"flatten: unexpected: $x")
    case x: SEWronglyTypeContractId => throw CompilationError(s"flatten: unexpected: $x")
    case x: SEImportValue => throw CompilationError(s"flatten: unexpected: $x")
    case x: SEVar => throw CompilationError(s"flatten: unexpected: $x")

  }


  def atomizeExps(depth: Int, env: Env, exps: List[SExpr], k: K[List[Atom]]): Res = exps match {
    case Nil => k(env,Nil)
    case exp::exps =>
      atomizeExp(depth, env, exp, { case (env,atom) =>
        atomizeExps(depth, env, exps, { case (env,atoms) =>
          k(env, atom::atoms)
        })
      })
  }

  def atomizeExp(depth: Int, env: Env, exp: SExpr, k: K[Atom]): Res = {
    //println(s"atomizeExp(depth=$depth,env=$env,exp=$exp")
    exp match {
      case atom: SExprAtomic =>
        k (env, Left(atom))
      case _ =>
        transformExp(depth, env, exp, { case (env, exp) =>
          val (env1,newBinding) = makeNewBinding(env)
          //println(s"atomizeExp/makeNewBinding(exp=$exp) -> env1=$env1, newbinding=$newBinding")
          SELet(Array(exp), k(env1, Right(newBinding)))
        })
    }
  }

}
