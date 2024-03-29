package software
package example.xiangshan

import librarySimUInt._

case class C22Inputs(io_in: Seq[UInt])
case class C22Outputs(io_out: Seq[UInt])
case class C22Regs()

case class C22() {
  def inputsRequire(inputs: C22Inputs): Boolean = inputs match {
    case C22Inputs(io_in) =>
      io_in.length == 2 &&
      io_in.forall(_.width == 1)
  }
  def outputsRequire(outputs: C22Outputs): Boolean = outputs match {
    case C22Outputs(io_out) =>
      io_out.length == 2 &&
      io_out.forall(_.width == 1)
  }
  def regsRequire(regs: C22Regs): Boolean = regs match {
    case C22Regs() =>
      true
  }

  def trans(inputs: C22Inputs, regs: C22Regs): (C22Outputs, C22Regs) = {
    require(inputsRequire(inputs) && regsRequire(regs))

    // output
    var io_out = Seq.fill(2)(UInt.empty(1))

    // body
    var temp = Seq.fill(1)(UInt.empty(2))
    (0 until temp.length).foreach((i: Int) => {
      val (a, b) = (inputs.io_in(0)(i), inputs.io_in(1)(i))
      val sum = (a ^ b)
      val cout = (a & b)
      temp = temp.updated[UInt, Seq[UInt]](i, temp(i) := Cat(cout, sum))
    })
    (0 until io_out.length).foreach((i: Int) => io_out = io_out.updated[UInt, Seq[UInt]](i, io_out(i) := Cat(temp.reverse.map((x$2: UInt) => x$2(i)))))

    (
      C22Outputs(io_out),
      C22Regs()
    )
  }

  def c22Run(timeout: Int, inputs: C22Inputs, regInit: C22Regs): (C22Outputs, C22Regs) = {
    require(timeout >= 1 && inputsRequire(inputs) && regsRequire(regInit))
    val (newOutputs, newRegs) = trans(inputs, regInit)
    if (timeout > 1) {
      c22Run(timeout - 1, inputs, newRegs)
    } else {
      (newOutputs, newRegs)
    }
  }
  def run(inputs: C22Inputs, randomInitValue: C22Regs): (C22Outputs, C22Regs) = {
    require(inputsRequire(inputs) && regsRequire(randomInitValue))
    val regInit = C22Regs()
    c22Run(100, inputs, regInit)
  }
}
