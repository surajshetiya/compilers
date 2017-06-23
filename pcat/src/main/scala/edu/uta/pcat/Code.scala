/****************************************************************************************************
 *
 * File: Code.scala
 * The IR code generator for PCAT programs
 *
 ****************************************************************************************************/

package edu.uta.pcat

import scala.collection.mutable.Stack

abstract class CodeGenerator ( tc: TypeChecker )  {
  def typechecker = tc
  def st = tc.st
  def code ( e: ProcDecl ): IRstmt
  def allocate_variable ( name: String, var_type: Type, fname: String ): IRexp
}


class Code ( tc: TypeChecker ) extends CodeGenerator(tc) {

  /** holds the exit labels of loops (needed for the exit() statements) */
  var labels = new Stack[String]

  var name_counter = 0

  /** generate a new variable name */
  def new_name ( name: String ): String = {
    name_counter += 1
    name + "_" + name_counter
  }

  /** allocate a new variable at the end of the current frame and return the access code */
  def allocate_variable ( name: String, var_type: Type, fname: String ): IRexp = {
    st.lookup(fname) match {
      case Some(ProcDec(rtp,params,label,level,min_offset)) => {
          // allocate variable at the next available offset in frame
          st.insert(name,VarDec(var_type,level,min_offset))
          // the next available offset in frame is 4 bytes below
          st.replace(fname,ProcDec(rtp,params,label,level,min_offset-4))
          // return the code that accesses the variable
          Mem(Binop("PLUS",Reg("fp"),IntValue(min_offset)))
      }
      case _ => throw new Error("No current function: " + fname)
    }
  }

  /** access a frame-allocated variable from the run-time stack */
  def access_variable ( name: String, level: Int ): IRexp = {
    st.lookup(name) match {
      case Some(VarDec(_,var_level,offset)) => {
        var res: IRexp = Reg("fp")
        // non-local variable: follow the static link (level-var_level) times
        for ( i <- var_level+1 to level )
            res = Mem(Binop("PLUS",res,IntValue(-8)))
        Mem(Binop("PLUS",res,IntValue(offset)))
      }
      case _ => throw new Error("Undefined variable: " + name)
    }
  }

  /** return the IR code from the Expr e (level is the current function nesting level,
   *  fname is the name of the current function/procedure) */
  def code ( e: Expr, level: Int, fname: String ): IRexp = {
    e match {
      case BinOpExp(op,left,right) => {
          val cl = code(left,level,fname)
          val cr = code(right,level,fname)
          val nop = op.toUpperCase()
          Binop(nop,cl,cr)
      }
      case ArrayExp(nm,inits) => {
        // A is the array address
        val A = allocate_variable(new_name("A"),NamedType(nm),fname)
        // I is offset of end-of-array
        val I = allocate_variable(new_name("I"),typechecker.intType,fname)
        // for iterating through loops
        val i = allocate_variable(new_name("i"),typechecker.intType,fname)
        // IR that calculates the array length
        var len: IRexp = IntValue(0)
        var cs: List[IRstmt] = List()
        for ( (n,v) <- inits )
          if (n == IntConst(1)) {   // don't need a loop for this
              val cv = code(v,level,fname)
              len = Binop("PLUS",len,IntValue(1))
              cs = cs :+ Seq(List(Move(Mem(Binop("PLUS",A,I)),cv),
                                  Move(I,Binop("PLUS",I,IntValue(4)))))
          } else {
            val cn = code(n,level,fname)
            val cv = code(v,level,fname)
            val loop = new_name("loop")
            val exit = new_name("exit")
            len = Binop("PLUS",len,cn)
            cs = cs :+ Seq(List(Move(i,IntValue(0)),
                                Label(loop),          // a for-loop
                                CJump(Binop("GEQ",i,cn),exit),
                                Move(Mem(Binop("PLUS",A,I)),cv),
                                Move(I,Binop("PLUS",I,IntValue(4))),
                                Move(i,Binop("PLUS",i,IntValue(1))),
                                Jump(loop),
                                Label(exit)))
          }
        ESeq(Seq(List(Move(A,Allocate(Binop("PLUS",len,IntValue(1)))),    // allocate len+1 words for A
                      Move(Mem(A),len),         // set the array length
                      Move(I,IntValue(4)))      // first available offset is 4
                 ++ cs),
             A)
      }
      
      case UnOpExp ( op, operand ) =>  {
        val operand_ir = code(operand,level,fname)
        val nop = op.toUpperCase()
        Unop(nop,operand_ir)
      }
      
      case LvalExp ( lvalue ) => {
        lvalue match {
          case Var("TRUE") => IntValue(1)
          case Var("FALSE") => IntValue(0)
          case Var("NIL") => IntValue(0)
          case _ => code(lvalue, level, fname)
        }
      }
      
      case CallExp ( name: String, arguments: List[Expr] ) => {
        val call_st = st.lookup(name) match {
          case Some(ProcDec(_, _, n, l, _)) => (n,l)
          case _ => throw new Error("Expected ProcDec")
        }
        val call_name = call_st._1
        val call_level = call_st._2
        var level_diff = 1
        var static_link = Mem(Binop("PLUS", Reg("fp"), IntValue(-8)))
        while(level_diff < level - call_level){
          static_link = Mem(Binop("PLUS", static_link, IntValue(-8)))
          level_diff = level_diff + 1
        }
        Call(call_name, static_link, arguments.map(x => code(x, level, fname)))
      }
      
      case RecordExp ( name: String, arguments: List[(String,Expr)] ) => {
        var R = allocate_variable(new_name("R"),NamedType(name),fname)
        def get_offset(comp:List[(String, String)], attr:String, value: Int):Int = {
          if(attr == comp.head._1) value
          else get_offset(comp.tail, attr, value+4)
        }
        val components = st.lookup(name) match {
          case Some(TypeDec(RecordType(t))) => t
          case _ => throw new Error("Expected record type")
        }
        var ret = List[IRstmt]()
        for(a <- arguments) {
           ret = ret :+ Move(
             Mem(Binop("PLUS", R, IntValue(get_offset(components, a._1, 0)))),
             code(a._2, level, fname))
        }
        ESeq( Seq(ret), R)
      }
      
      case IntConst ( value ) => {
        IntValue(value)
      }
      
      case RealConst ( value ) => {
        RealValue( value )
      }
      
      case StringConst ( value ) => {
        StringValue( value )
      }
      /* PUT YOUR CODE HERE */

      case _ => throw new Error("Wrong expression: "+e)
    }
  }

  /** return the IR code from the Statement e (level is the current function nesting level,
   *  fname is the name of the current function/procedure) */
  def code ( e: Stmt, level: Int, fname: String ): IRstmt = {
    e match {
      case AssignSt(v,u) => {
            val cd = code(v,level,fname)
            val cs = code(u,level,fname)
            Move(cd,cs)
      }
      
      case CallSt( name: String, arguments: List[Expr] ) => {
        val call_st = st.lookup(name) match {
          case Some(ProcDec(_, _, n, l, _)) => (n,l)
          case _ => throw new Error("Expected ProcDec")
        }
        val call_name = call_st._1
        val call_level = call_st._2
        var level_diff = 1
        var static_link = Mem(Binop("PLUS", Reg("fp"), IntValue(-8)))
        while(level_diff < level - call_level){
          static_link = Mem(Binop("PLUS", static_link, IntValue(-8)))
          level_diff = level_diff + 1
        }
        CallP(call_name, static_link, arguments.map(x => code(x, level, fname)))
      }
      
      case ReadSt ( arguments: List[Lvalue] ) => {
        var list_args = List[IRstmt]()
        for (a <- arguments){
          typechecker.typecheck(a) match {
            case NamedType("INTEGER") => list_args = list_args :+ SystemCall("READ_INT",code(a, level, fname))
            case NamedType("STRING") => list_args = list_args :+ SystemCall("READ_STRING",code(a, level, fname))
            case NamedType("FLOAT") => list_args = list_args :+ SystemCall("READ_FLOAT",code(a, level, fname))
            case _ => throw new Error("Cannot read other type of data")
          }
        }
        Seq(list_args)
      }
      
      case WriteSt ( arguments: List[Expr] ) => {
        var list_args = List[IRstmt]()
        for (a <- arguments){
          a match {
            case IntConst(v) => list_args = list_args :+ SystemCall("WRITE_INT", IntValue(v))
            case StringConst(v) => list_args = list_args :+ SystemCall("WRITE_STRING", StringValue(v))
            case RealConst(v) => list_args = list_args :+ SystemCall("WRITE_FLOAT", RealValue(v))
            case _ =>  typechecker.typecheck(a) match {
              case NamedType("INTEGER") => list_args = list_args :+ SystemCall("WRITE_INT",code(a, level, fname))
              case NamedType("STRING") => list_args = list_args :+ SystemCall("WRITE_STRING",code(a, level, fname))
              case NamedType("FLOAT") => list_args = list_args :+ SystemCall("WRITE_FLOAT",code(a, level, fname))
              case _ => throw new Error("Cannot write other type of data")
            }
          }
        }
        list_args = list_args :+ SystemCall("WRITE_STRING",StringValue("\\n"))
        Seq(list_args)
      }
      
      case IfSt ( condition: Expr, then_stmt: Stmt, else_stmt: Stmt ) => {
        //val start_label = new_name("start_label")
        val else_label = new_name("else_label")
        val exit_label = new_name("exit_label")
        labels.push(exit_label)
        def elseif( stmt:Stmt ):IRstmt = {
          stmt match {
            case IfSt(c, t, e) => {
              val else_label = new_name("else_label")
              Seq(List[IRstmt](CJump(Unop("NOT", code(c, level, fname)), else_label), 
              code(t, level, fname), Jump(labels.top), Label(else_label),
              elseif(e)))
            }
            case _ => code(stmt, level, fname)
          }
        }
        val id_seq = Seq(List[IRstmt](CJump(Unop("NOT", code(condition, level, fname)), else_label),
        code(then_stmt, level, fname), Jump(exit_label), Label(else_label),
        elseif(else_stmt), Label(exit_label)))
        labels.pop()
        id_seq
        /*Seq(List[IRstmt](CJump(code(condition, level, fname), start_label), Jump(else_label),
          Label(start_label), code(then_stmt, level, fname), Jump(exit_label),
          Label(else_label), code(else_stmt, level, fname), Label(exit_label)))*/
      }
      
      case WhileSt ( condition: Expr, body: Stmt ) => {
        val exit_label = new_name("exit_label")
        val start_label = new_name("start_label")
        labels.push(exit_label)
        val body_code = code(body, level, fname)
        // TODO: Should body_code be expanded if it is Seq
        val while_seq = List[IRstmt](Label(start_label),
          CJump(Unop("NOT", code(condition, level, fname)), exit_label),
          body_code, Jump(start_label), Label(exit_label))
        labels.pop()
        Seq(while_seq)
      }
      
      case LoopSt ( body: Stmt ) => {
        val start_label = new_name("start_label")
        val exit_label = new_name("exit_label")
        labels.push(exit_label)
        val body_code = List[IRstmt](Label(start_label), code(body, level, fname),
            Jump(start_label), Label(exit_label))
        labels.pop()
        Seq(body_code)
      }
      
      case ForSt ( variable: String, initial: Expr, step: Expr, increment: Expr, body: Stmt ) => {
        // TODO: Something wrong here. var_for not present within the return
        //       statement.
        var exit_variable = new_name("exit_variable")
        // Create a new variable to store upper value in order to stop side effects
        val var_for = allocate_variable(variable, NamedType("INTEGER"), fname)
        val exit_var = allocate_variable(exit_variable, NamedType("INTEGER"), fname)
        val exit_label = new_name("exit_label")
        val start_label = new_name("start_label")
        labels.push(exit_label)
        val for_st = List[IRstmt](Move(Mem(var_for), code(initial, level, fname)),
          Move(Mem(exit_var), code(step, level, fname)), Label(start_label),
          CJump(Binop("GT", var_for, exit_var), exit_label),
          code(body, level, fname),Move(Mem(var_for),code(increment, level, fname)), Jump(start_label),
          Label(exit_label))
        labels.pop()
        Seq(for_st)
      }
      
      case ExitSt () => {
        Jump(labels.top)
      }
      
      case ReturnValueSt ( value: Expr ) => {
        
        Seq(List(Move(Reg("a0"), code(value, level, fname)),
        Move(Reg("ra"),Mem(Binop("PLUS",Reg("fp"),IntValue(-4)))),
          Move(Reg("sp"),Reg("fp")), Move(Reg("fp"),Mem(Reg("fp"))), Return()))
      }
      
      case ReturnSt () => {
        Seq(List(Move(Reg("ra"),Mem(Binop("PLUS",Reg("fp"),IntValue(-4)))),
          Move(Reg("sp"),Reg("fp")), Move(Reg("fp"),Mem(Reg("fp"))), 
          Return()))
      }
      
      case SeqSt ( stmts ) => {
        var ret = List[IRstmt]()
        for( s <- stmts )
         ret = ret :+ code(s, level, fname)
        Seq(ret)
      }
      /* PUT YOUR CODE HERE */

      case _ => throw new Error("Wrong statement: " + e)
    }
  }

  /** return the IR code from the Lvalue e (level is the current function nesting level,
   *  fname is the name of the current function/procedure) */
  def code ( e: Lvalue, level: Int, fname: String ): IRexp = {
    e match {
      case Var(s) => access_variable(s,level)
      
      case ArrayDeref ( array: Lvalue, index: Expr ) => {
        Assert(Binop("GEQ", code(index, level, fname), IntValue(0)))
        Assert(Binop("LT", code(index, level, fname), code(array, level, fname)))
        val memory_value = code(array, level, fname) match {
          case Mem(x) => x
          case _ => throw new Error("Unexpected value found in record deref")
        }
        Mem(Binop("PLUS", memory_value, Binop("TIMES", IntValue(4),
              Binop("PLUS", code(index, level, fname),IntValue(1)))))
      }
      
      case RecordDeref ( record: Lvalue, attribute: String ) => {
        Assert(Binop("NE", code(record, level, fname), IntValue(0)))
        val memory_value = code(record, level, fname) match  {
          case Mem(x) => x
          case _ => throw new Error("Unexpected value found in record deref")
        }
        val comp = typechecker.expandType(typechecker.typecheck(record)) match {
          case RecordType(c) => c
          case _ => throw new Error("Expected a record type here")
        }
        def get_offset(comp:List[(String, String)], attr:String, value: Int):Int = {
          if(attr == comp.head._1) value
          else get_offset(comp.tail, attr, value+4)
        }
        Mem(Binop("PLUS", memory_value, IntValue(get_offset(comp, attribute, 0))))
      }
      /* PUT YOUR CODE HERE */

      case _ => throw new Error("Wrong statement: " + e)
    }
  }

  /** return the IR code from the function body (level is the current function nesting level,
   *  f is the name of the current function/procedure) */
  def code ( e: Body, level: Int, f: String ): IRstmt = {
    e match {
      case Body(ds,s) => {
        val defs = Seq(ds.map(code(_,f,level)))
        val body = Seq(s.map(code(_,level,f)))
        val inits = Seq(for ( VarDecls(vds) <- ds;
                              VarDecl(vs,_,u) <- vds;
                              uc = code(u,level,f);
                              v <- vs )
                            yield Move(access_variable(v,level),uc))
        st.lookup(f) match {
          case Some(ProcDec(_,_,fname,_,offset))
            => Seq(List(defs,
                        Label(fname),
                        Move(Mem(Reg("sp")),Reg("fp")),
                        Move(Reg("fp"),Reg("sp")),
                        Move(Mem(Binop("PLUS",Reg("fp"),IntValue(-4))),Reg("ra")),
                        Move(Mem(Binop("PLUS",Reg("fp"),IntValue(-8))),Reg("v0")),
                        Move(Reg("sp"),Binop("PLUS",Reg("sp"),IntValue(offset))),
                        inits,
                        body,
                        Move(Reg("ra"),Mem(Binop("PLUS",Reg("fp"),IntValue(-4)))),
                        Move(Reg("sp"),Reg("fp")),
                        Move(Reg("fp"),Mem(Reg("fp"))),
                        Return()))
          case _ => throw new Error("Unkown function: "+f)
        }
      }
    }
  }

  /** return the IR code for the declaration block of function fname
   * (level is the current function nesting level) */
  def code ( e: Declaration, fname: String, level: Int ): IRstmt = {
    e match {
      case TypeDecls(tds) => {
        for ( TypeDecl(n,t) <- tds )
              st.insert(n,TypeDec(t))
        Seq(List())
      }
      case VarDecls(vds) => {
        for ( VarDecl(vs,t,u) <- vds; v <- vs )
              if (t == "NoType")
                allocate_variable(v,typechecker.typecheck(u),fname)
              else allocate_variable(v,NamedType(t),fname)
        Seq(List())
      }
      case ProcDecls(pds) => {
        for ( ProcDecl(f,ot,ps,b) <- pds )
            st.insert(f,ProcDec(NamedType(ot),
                                ps.flatMap({
                                    case (vs,t) => vs.map(_ -> NamedType(t))
                                }),new_name(f),level+1,-12))
        Seq( for ( ProcDecl(f,ot,ps,b) <- pds ) yield {
                var i = 4
                st.begin_scope()
                for ( (vs,t) <- ps.reverse; v <- vs.reverse ) {
                      st.insert(v,VarDec(NamedType(t),level+1,i))
                      i += 4
                }
                val res = code(b,level+1,f)
                st.end_scope()
                res
            } )
      }
    }
  }

  /** generate code for the main program */
  def code ( e: ProcDecl ): IRstmt = {
    e match {
      case ProcDecl(f,ot,ps,b) => {
          var i = 4
          st.begin_scope()
          st.insert(f,ProcDec(NamedType(ot),List(),f,1,-12))
          val res = code(b,1,f)
          st.end_scope()
          res
      }
    }
  }

}
