/****************************************************************************************************
 *
 * File: MIPS.scala
 * Generation of MIPS code from IR code
 *
 ****************************************************************************************************/

package edu.uta.pcat

/** representation of a MIPS register */
case class Register ( val reg: String ) {
    override def toString (): String = reg
}


/** a pool of available registers */
class RegisterPool {

  val all_registers
        = List( "$t0", "$t1", "$t2", "$t3", "$t4", "$t5", "$t6", "$t7", "$t8", "$t9",
                "$s0", "$s1", "$s2", "$s3", "$s4", "$s5", "$s6", "$s7" )

  var available_registers = all_registers.map(Register(_))

  /** is register reg temporary? */
  def is_temporary ( reg: Register ): Boolean =
    reg match {
      case Register(n) => all_registers.contains(n)
    }

  /** return the next available temporary register */
  def get (): Register =
    available_registers match {
      case reg::rs => {
        available_registers = rs
        reg
      }
      case _ => throw new Error("*** Run out of registers")
    }

  /** recycle (put back into the register pool) the register reg (if is temporary) */
  def recycle ( reg: Register ) {
    if (available_registers.contains(reg))
      throw new Error("*** Register has already been recycled: "+reg)
    if (is_temporary(reg))
      available_registers = reg::available_registers
  }

  /** return the list of all temporary registers currently in use */
  def used (): List[Register] = {
    for ( reg <- all_registers
          if (!available_registers.contains(Register(reg))) )
      yield Register(reg)
  }
}


abstract class MipsGenerator {
  def clear ()
  def emit ( e: IRstmt )
}


class Mips extends MipsGenerator {

  var assert_count = 0

  /** emit a MIPS label */
  def mips_label ( s: String ) {
    PCAT.out.println(s + ":")
  }

  /** emit MIPS code with no operands */
  def mips ( op: String ) {
    PCAT.out.println("        " + op)
  }

  /** emit MIPS code with operands */
  def mips ( op: String, args: String ) {
    PCAT.out.print("        " + op)
    for ( i <- op.length to 10)
        PCAT.out.print(" ")
    PCAT.out.println(args)
  }

  /** a pool of temporary registers */
  var rpool = new RegisterPool

  /** clear the register pool */
  def clear () {
    rpool = new RegisterPool
  }

  var name_counter = 0

  /** generate a new  label name */
  def new_label (): String = {
    name_counter += 1
    "L_" + name_counter
  }

  /** generate MIPS code from the IR expression e and return the register that will hold the result */
  def emit ( e: IRexp ): Register = {
    e match {
      case Mem(Binop("PLUS",Reg(r),IntValue(n))) => {
        val reg = rpool.get()
        mips("lw",reg + ", " + n + "($" + r + ")")
        reg
      }
      case Mem(x) => {
        val reg = emit(x)
        mips("lw", reg + ", (" + reg +")")
        reg
      }
      case Reg(r) => {
        val reg = rpool.get()
        mips("move", reg + ", $" + r)
        reg
      }
      case Binop("PLUS",x,y) => {
        val left = emit(x)
        val right = emit(y)
        mips("addu", left+", "+left+", "+right)
        rpool.recycle(right)
        left
      }
      case Binop("MINUS",x,y) => {
        val left = emit(x)
        val right = emit(y)
        mips("subu", left+", "+left+", "+right)
        rpool.recycle(right)
        left
      }
      case Binop("MOD",x,y) => {
        val left = emit(x)
        val right = emit(y)
        mips("rem", left+", "+left+", "+right)
        rpool.recycle(right)
        left
      }
      case Binop("TIMES",x,y) => {
        val left = emit(x)
        val right = emit(y)
        mips("mul", left+", "+left+", "+right)
        rpool.recycle(right)
        left
      }
      case Binop("DIV",x,y) => {
        val left = emit(x)
        val right = emit(y)
        mips("divu", left+", "+left+", "+right)
        rpool.recycle(right)
        left
      }
      case Binop("LT",x,y) => {
        val left = emit(x)
        val right = emit(y)
        mips("slt", left+", "+left+", "+right)
        rpool.recycle(right)
        left
      }
      case Binop("LEQ",x,y) => {
        val left = emit(x)
        val right = emit(y)
        mips("sle", left+", "+left+", "+right)
        rpool.recycle(right)
        left
      }
      case Binop("GEQ",x,y) => {
        val left = emit(x)
        val right = emit(y)
        mips("sge", left+", "+left+", "+right)
        rpool.recycle(right)
        left
      }
      case Binop("GT",x,y) => {
        val left = emit(x)
        val right = emit(y)
        mips("sgt", left+", "+left+", "+right)
        rpool.recycle(right)
        left
      }
      case Binop("EQ",x,y) => {
        val left = emit(x)
        val right = emit(y)
        mips("seq", left+", "+left+", "+right)
        rpool.recycle(right)
        left
      }
      case Binop("NEQ",x,y) => {
        val left = emit(x)
        val right = emit(y)
        mips("sne", left+", "+left+", "+right)
        rpool.recycle(right)
        left
      }
      case Binop("AND",x,y) => {
        val label = new_label()
        val left = emit(x)
        val reg = left
        mips("beq",left+", 0, "+label)
        val right = emit(y)
        mips("move",left+", "+right)
        mips_label(label)
        rpool.recycle(right)
        reg
      }
      case Binop("OR",x,y) => {
        val label = new_label()
        val left = emit(x)
        val reg = left
        mips("beq",left+", 1, "+label)
        val right = emit(y)
        mips("move",left+", "+right)
        mips_label(label)
        rpool.recycle(right)
        reg
      }
      case Unop("NOT", x) => {
        val reg = emit(x)
        mips("xori", reg+", "+reg+", 1")
        reg
      }
      case Unop("MINUS", x) => {
        val reg = emit(x)
        mips("neg", reg+", "+reg)
        reg
      }
      case IntValue(i) => {
        val reg = rpool.get()
        mips("li", reg + ", " + i)
        reg
      }
      case StringValue(s) => {
        val label = new_label()
        val reg = rpool.get()
        mips(".data", "")
        mips(".align", "2");
        mips_label(label)
        mips(".asciiz", "\"" + s + "\"")
        mips(".text", "")
        mips("la", reg +", " + label)
        reg
      }
      case Call(f,sl,args) => {
        val used_regs = rpool.used()
        val size = (used_regs.length+args.length)*4
        /* allocate space for used temporary registers */
        if (size > 0)
            mips("subu","$sp, $sp, "+size)
        /* push the used temporary registers */
        var i = size
        for (r <- used_regs) {
            mips("sw",r + ", " + i + "($sp)")
            i -= 4
        }
        /* push arguments */
        i = args.length*4
        for (a <- args) {
          val reg = emit(a)
          mips("sw",reg + ", " + i + "($sp)")
          rpool.recycle(reg)
          i -= 4
        }
        /* set $v0 to be the static link */
        val sreg = emit(sl)
        mips("move","$v0, " + sreg)
        rpool.recycle(sreg)
        mips("jal",f)
        i = size
        /* pop the used temporary registers */
        for (r <- used_regs) {
            mips("lw",r + ", " + i + "($sp)")
            i -= 4
        }
        /* deallocate stack from args and used temporary registers */
        if (size > 0)
            mips("addu","$sp, $sp, "+size)
        val res = rpool.get()
        mips("move",res + ", $a0")
        /* You shouldn't just return $a0 */
        res
      }
      case Allocate(a) => {
        val reg = emit(a)
        val r1 = rpool.get()
        mips("li", r1 + ", 4")
        mips("mul", reg + ", " + r1 + ", " + reg)
        // reg - space needed
        mips("move", r1 + ", $gp")
        //Expand gp to new location
        mips("addu", "$gp, $gp, " + reg)
        rpool.recycle(reg)
        r1
      }
      /* PUT YOUR CODE HERE */

      case _ => throw new Error("Unknown IR: "+e)
    }
  }

  /** generate MIPS code from the IR statement e */
  def emit ( e: IRstmt ) {
    e match {
      case Move(Mem(Binop("PLUS",Reg(r),IntValue(n))),u) => {
        val src = emit(u)
        mips("sw",src + ", " + n + "($" + r + ")")
        rpool.recycle(src)
      }
      case Move(Reg(r), v) => {
        val src = emit(v)
        mips("move", "$" + r + ", " + src)
        rpool.recycle(src)
      }
      case Move(Mem(m), v) => {
        val src = emit(v)
        val dst = emit(m)
        mips("sw",src + ", (" + dst + ")")
        rpool.recycle(src)
        rpool.recycle(dst)
      }
      case Label(l) => {
        mips_label(l)
      }
      case Jump(l) => {
        mips("j", l)
      }
      case CJump(c, l) => {
        val reg = emit(c)
        mips("bne", reg + ", $zero ," +l)
        rpool.recycle(reg)
      }
      case CallP(f,sl,args) => {
        val used_regs = rpool.used()
        val size = (used_regs.length+args.length)*4
        /* allocate space for used temporary registers */
        if (size > 0)
            mips("subu","$sp, $sp, "+size)
        /* push the used temporary registers */
        var i = size
        for (r <- used_regs) {
            mips("sw",r + ", " + i + "($sp)")
            i -= 4
        }
        /* push arguments */
        i = args.length*4
        for (a <- args) {
          val reg = emit(a)
          mips("sw",reg + ", " + i + "($sp)")
          rpool.recycle(reg)
          i -= 4
        }
        /* set $v0 to be the static link */
        val sreg = emit(sl)
        mips("move","$v0, " + sreg)
        rpool.recycle(sreg)
        mips("jal",f)
        i = size
        /* pop the used temporary registers */
        for (r <- used_regs) {
            mips("lw",r + ", " + i + "($sp)")
            i -= 4
        }
        /* deallocate stack from args and used temporary registers */
        if (size > 0)
            mips("addu","$sp, $sp, "+size)
        // TODO: Should I release a0 here ?
      }
      case Return() => {
        mips("jr", "$ra")
      }
      case Assert(cond) => {
        val reg = emit(cond)
        mips("beq",reg+", 0, Assertion_failure")
        rpool.recycle(reg)
      }
      case SystemCall("WRITE_STRING", str) => {
        val reg = emit(str)
        mips("li", "$v0, 4")
        mips("move", "$a0, " + reg)
        mips("syscall", "")
        rpool.recycle(reg)
      }
      case SystemCall("WRITE_INT", value) => {
        val reg = emit(value)
        mips("move", "$a0, " + reg)
        mips("li", "$v0, 1")
        mips("syscall", "")
        rpool.recycle(reg)
      }
      case SystemCall("READ_INT", value) => {
        mips("li", "$v0, 5")
        mips("syscall", "")
        val loc_reg = emit(value)
        mips("sw", "$v0, ("+ loc_reg  +")")
      }
      /* PUT YOUR CODE HERE */

      case _ => throw new Error("Unknown IR: "+e)
    }
  }
}
