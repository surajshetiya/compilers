/****************************************************************************************************
 *
 * File: TypeCheck.scala
 * The type-checker for PCAT programs
 *
 ****************************************************************************************************/

package edu.uta.pcat

import scala.collection.immutable.ListMap


abstract class TypeChecker {
  var trace_typecheck = false

  /** symbol table to store PCAT declarations */
  var st = new SymbolTable

  /* various types */
  val anyType    = AnyType()
  val noType     = NamedType("NoType")
  val intType    = NamedType("INTEGER")
  val boolType   = NamedType("BOOLEAN")
  val floatType  = NamedType("FLOAT")
  val stringType = NamedType("STRING")

  def expandType ( tp: Type ): Type
  def typecheck ( e: Expr ): Type
  def typecheck ( e: Lvalue ): Type
  def typecheck ( e: Stmt )
  def typecheck ( e: Body, returned: Type )
  def typecheck ( e: ProcDecl )
}


class TypeCheck extends TypeChecker {

  /** the expected type of the return value from the current function */
  var expected_returned_type: Type = null

  /** If tp is a named type, expand it */
  def expandType ( tp: Type ): Type = {
    if (tp.equals(intType) || tp.equals(boolType)
        || tp.equals(floatType) || tp.equals(stringType)
        || tp.equals(anyType) || tp.equals(noType))
      tp
    else tp match {
      case NamedType(nm)
        => st.lookup(nm) match {
          case Some(TypeDec(t))
              => expandType(t)
          case _ => throw new Error("Undeclared type: "+tp)
        }
      case _ => tp
    }
  }

  /** returns true if the types tp1 and tp2 are equal under name equivalence */
  def typeEquivalence ( tp1: Type, tp2: Type ): Boolean = {
    /* AnyType() matches any RecordType(...) */
    if (tp1.equals(tp2))
      true
    else expandType(tp1) match {
      case RecordType(_)
        => tp2.equals(anyType)
      case _ => expandType(tp2) match {
        case RecordType(_)
            => tp1.equals(anyType)
        case _ => false
      }
    }
  }

  /* Tracing level */
  var level: Int = -1

  def trace[T] ( e: Any, result: => T ): T = {
    if (trace_typecheck) {
      level += 1
      println(" "*(3*level)+"** "+e)
    }
    val res = result
    if (trace_typecheck) {
      print(" "*(3*level))
      if (res == ())
        println("->")
      else println("-> "+res)
      level -= 1
    }
    res
  }

  /** typecheck an expression AST */
  def typecheck ( e: Expr ): Type =
    trace(e,e match {
      case BinOpExp(op,l,r) => {
        val ltp = typecheck(l)
        val rtp = typecheck(r)
        if (!typeEquivalence(ltp,rtp))
          throw new Error("Incompatible types in binary operation: "+e)
        else if (op.equals("and") || op.equals("or"))
               if (typeEquivalence(ltp,boolType))
                 ltp
               else throw new Error("AND/OR operation can only be applied to booleans: "+e)
               else if (op.equals("eq") || op.equals("neq"))
                      boolType
               else if (!typeEquivalence(ltp,intType) && !typeEquivalence(ltp,floatType))
                      throw new Error("Binary arithmetic operations can only be applied to integer or real numbers: "+e)
               else if (op.equals("gt") || op.equals("lt") || op.equals("geq") || op.equals("leq"))
                      boolType
               else ltp
      }
      case UnOpExp(op, operand) => {
        val value = typecheck(operand)
   
        if(op.equals("not")){
          if (!typeEquivalence(value,boolType))
            throw new Error("Unary NOT operation can only be applied to boolean: "+e)
          boolType
        } else if(op.equals("minus")){
          if (!typeEquivalence(value,intType))
            throw new Error("Unary MINUS operation can only be applied to integer or real number: "+e)
          value
        } else 
          throw new Error("Unknown Unary Operator:"+e)
      }
      case LvalExp(lvalue) => typecheck(lvalue)
      case IntConst(_) => intType
      case RealConst(_) => floatType
      case StringConst(_) => stringType
      case CallExp(name, args) => {
        st.lookup(name) match {
          case Some(ProcDec(ret_typ,params,_,_,_)) => {
            if(params.length != args.length)
              throw new Error("Function parameters length do not match!" + args)
            val p = params map {_._2} // case (_,x) => x
            for( (ar,par) <- args.zip(p))
              if(!typeEquivalence(expandType(par), expandType((typecheck(ar)))))
                throw new Error("Types do not match! " + typecheck(ar) + " " + par)
            ret_typ
          }
          case Some(_) => throw new Error(name+" is not a function declaration")
          case None => throw new Error("Undefined function: "+name)
        }
      }
      // RecordExp ( name: String, arguments: List[(String,Expr)] )
      // Rec: List[(String, Type)]
      case RecordExp(name, args) => {
        val ty = st.lookup(name) match {
          case Some(TypeDec(RecordType(t))) => t
          case Some(_) => throw new Error(name+" is not a variable")
          case None => throw new Error("Undefined variable: "+e)
        }
        val ty_types = ty map { case (x,y) => (x, NamedType(y)) }
        if(args.length != ty.length)
          throw new Error("Record fields length do not match: "+e)
          
        def check_record(rec:(String, Type), list_exp:List[(String, Expr)]): Boolean = {
          list_exp match {
            case (s,e)::tail => {
              if(s == rec._1) {
                if(!typeEquivalence(expandType(rec._2), expandType(typecheck(e)))) throw new Error("Types do not match"+rec._1)
                else true
              }
              else check_record(rec, tail)
            }
            case _ => throw new Error("Element not declared "+rec._1)
          }
        }
        for(r <- ty_types) 
          check_record(r, args)
        RecordType(ty)
      }
      
      // ArrayExp ( name: String, arguments: List[(Expr,Expr)] )
      case ArrayExp(name, args) => {
        val ty = st.lookup(name) match {
          case Some(TypeDec(ArrayType(t))) => t
          case Some(_) => throw new Error(name+" is not a variable")
          case None => throw new Error("Undefined variable: "+e)
        }
        for(a <- args) {
          if(!typeEquivalence(typecheck(a._1), intType))
            throw new Error("Expected integer at "+a)
          val targ = typecheck(a._2)
          if(!(typeEquivalence(targ, NamedType(ty)) || typeEquivalence(targ, expandType(NamedType(ty)))))
            throw new Error("Expected different type at "+typecheck(a._2)+NamedType(ty))
        }
        ArrayType(ty)
      }
      case _ => throw new Error("Wrong expression: "+e)
    } )

  /** typecheck an Lvalue AST */
  def typecheck ( e: Lvalue ): Type =
    trace(e,e match {
      case Var(name)=> {
        if(name == "TRUE" || name == "FALSE")
          boolType
        else if(name == "NIL")
          anyType
        else
          st.lookup(name) match {
            case Some(VarDec(t,_,_)) => t
            case Some(_) => throw new Error(name+" is not a variable")
            case None => throw new Error("Undefined variable: "+e)
        }
      }
      case ArrayDeref(array, index) => {
        val tarray = typecheck(array)
        if(!typeEquivalence(typecheck(index), intType))
          throw new Error("Expression does not yield an integer")
        tarray match {
          case ArrayType(t) => NamedType(t)
          case NamedType(t) => {
            st.lookup(t) match {
              case Some(TypeDec(ArrayType(typ))) => NamedType(typ)
              case Some(_) => throw new Error("Not a TYPE "+t)
              case None => throw new Error("Undefined variable: "+e)
            }
          }
          case _ => throw new Error("Unknown type encountered"+e)
        }
      }
      case RecordDeref(record, attribute) => {
        val trecord = typecheck(record)
        expandType(trecord) match{
          case RecordType(t) => {
             val m = t.filter(_._1 == attribute)
             m match {
               case (_,y)::t => NamedType(y)
               case _ => throw new Error("Did not find the variable"+attribute)
            }
          }
          case _ => throw new Error("Did not find record type"+trecord)
        }
      }

      case _ => throw new Error("Wrong lvalue: "+e)
    } )

  /** typecheck the body of a function */
  def typecheck ( e: Stmt ) {
    trace(e,
          e match {
      case AssignSt(d,s)
        => if (!typeEquivalence(expandType(typecheck(d)),expandType(typecheck(s))))
               throw new Error("Incompatible types in assignment: "+e)
      case IfSt(c, t, els) => {
        if(!typeEquivalence(typecheck(c),boolType))
          throw new Error("Condition should be booltype: "+e)
        typecheck(t)
        typecheck(els)
      }
      case ExitSt() => {}
      case ReturnValueSt(value) => typecheck(value)
      case ReturnSt() => {}
      case WhileSt(cond, s) => {
        if(!typeEquivalence(typecheck(cond),boolType))
          throw new Error("Condition should be booltype: "+e)
        typecheck(s)
      }
      case LoopSt(s) => typecheck(s)
      case ForSt(id,strt,end,by,s) => {
        st.begin_scope()
        st.insert(id, VarDec(NamedType("INTEGER"),1,1))
        typecheck(s)
        if(!(typeEquivalence(typecheck(strt),typecheck(end)) && typeEquivalence(typecheck(by),typecheck(end)) && 
            typeEquivalence(intType,typecheck(end)))) {
          throw new Error("Type not matching in For Statement: "+e)
        }
        st.end_scope()
      }
      case SeqSt(seq) => {
        for(st <- seq)
          typecheck(st)
      }
      case ReadSt(seq) => {
        for(st <- seq)
          typecheck(st)
      }
      case WriteSt(seq) => {
        for(st <- seq)
          typecheck(st)
      }
      case CallSt(name, args) => {
        st.lookup(name) match {
          case Some(ProcDec(_,params,_,_,_)) => {
            if(params.length != args.length)
              throw new Error("Function parameters length do not match!" + args)
            val p = params map {case (_,x) => x}
            for( (ar,par) <- args.zip(p))
              if(!typeEquivalence(expandType(par), expandType(typecheck(ar))))
                throw new Error("Types do not match! " + typecheck(ar) + " " + par)
          }
          case Some(_) => throw new Error(name+" is not a function declaration")
          case None => throw new Error("Undefined function: "+name)
        }
      }
      case _ => throw new Error("Wrong statement: "+e)
    } )
  }

  /** typecheck the body of a function */
  def typecheck ( e: Body, returned: Type ) {
    trace(e,
          e match {
      case Body(ds,s) => {
        ds.foreach(typecheck(_))
        expected_returned_type = returned
        s.foreach(typecheck(_))
      }
    } )
  }

  /** typecheck a declaration block */
  def typecheck ( e: Declaration ) {
    trace(e,
          e match {
      case TypeDecls(tds)
        => for ( TypeDecl(n,t) <- tds )
              st.insert(n,TypeDec(t))
      case VarDecls(vds)
        => for ( VarDecl(vs,t,u) <- vds; v <- vs )
                if (t == "NoType")
                  st.insert(v,VarDec(typecheck(u),0,0))
                else if (!typeEquivalence(expandType(typecheck(u)),expandType(NamedType(t))))
                       throw new Error("Incompatible types in variable declaration: "+NamedType(t))
                else st.insert(v,VarDec(NamedType(t),0,0))
      case ProcDecls(pds) => {
        for ( ProcDecl(f,ot,ps,b) <- pds )
            st.insert(f,ProcDec(NamedType(ot),
                                ps.flatMap({
                                    case (vs,t) => vs.map(_ -> NamedType(t))
                                }),"",0,0))
        for ( ProcDecl(f,ot,ps,b) <- pds ) {
          st.begin_scope()
          for ( (vs,t) <- ps; v <- vs )
              st.insert(v,VarDec(NamedType(t),0,0))
          typecheck(b,NamedType(ot))
          st.end_scope()
        }
      }
    } )
  }

  /** typecheck the main program */
  def typecheck ( e: ProcDecl ) {
    try {
      e match {
        case ProcDecl(f,ot,ps,b) => {
            st.begin_scope()
            typecheck(b,NamedType(ot))
            st.end_scope()
        }
      }
    } catch {
        case e: Error => println("*** Type checking error: " + e)
        sys.exit(-1)
    }
  }
}
