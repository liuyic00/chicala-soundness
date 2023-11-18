package software
package example.xiangshan

import librarySimUInt._

case class C53Inputs(io_in: Seq[UInt])
case class C53Outputs(io_out: Seq[UInt])
case class C53Regs()

case class C53() {
  def inputsRequire(inputs: C53Inputs): Boolean = inputs match {
    case C53Inputs(io_in) =>
      io_in.length == 5 &&
      io_in.forall(_.width == 1)
  }
  def outputsRequire(outputs: C53Outputs): Boolean = outputs match {
    case C53Outputs(io_out) =>
      io_out.length == 3 &&
      io_out.forall(_.width == 1)
  }
  def regsRequire(regs: C53Regs): Boolean = regs match {
    case C53Regs() =>
      true
  }

  def trans(inputs: C53Inputs, regs: C53Regs): (C53Outputs, C53Regs) = {
    require(inputsRequire(inputs) && regsRequire(regs))

    // output
    var io_out = Seq.fill(3)(UInt.empty(1))

    // body
    val FAs0 = example.xiangshan.C32()
    var FAs0_io_in = Seq.fill(3)(UInt.empty(1))
    var FAs0_io_out = Seq.fill(2)(UInt.empty(1))
    val FAs1 = example.xiangshan.C32()
    var FAs1_io_in = Seq.fill(3)(UInt.empty(1))
    var FAs1_io_out = Seq.fill(2)(UInt.empty(1))
    (0 until FAs0_io_in.length)
      .zip(inputs.io_in.take(3))
      .foreach { case (i, s) => FAs0_io_in = FAs0_io_in.updated[UInt, Seq[UInt]](i, FAs0_io_in(i) := s)}
    val (t$FAs0TransOutputs, _) = FAs0.trans(
      example.xiangshan.C32Inputs(FAs0_io_in),
      example.xiangshan.C32Regs()
    )
    FAs0_io_out = t$FAs0TransOutputs.io_out
    var tmp1 = Seq(FAs0_io_out(0), inputs.io_in(3), inputs.io_in(4))
    (0 until FAs1_io_in.length)
      .zip(tmp1)
      .foreach { case (i, s) => FAs1_io_in = FAs1_io_in.updated[UInt, Seq[UInt]](i, FAs1_io_in(i) := s)}
    val (t$FAs1TransOutputs, _) = FAs1.trans(
      example.xiangshan.C32Inputs(FAs1_io_in),
      example.xiangshan.C32Regs()
    )
    FAs1_io_out = t$FAs1TransOutputs.io_out
    var tmp2 = Seq(FAs1_io_out(0), FAs0_io_out(1), FAs1_io_out(1))
    (0 until io_out.length)
      .zip(tmp2)
      .foreach { case (i, s) => io_out = io_out.updated[UInt, Seq[UInt]](i, io_out(i) := s)}

    (
      C53Outputs(io_out),
      C53Regs()
    )
  }

  def c53Run(timeout: Int, inputs: C53Inputs, regInit: C53Regs): (C53Outputs, C53Regs) = {
    require(timeout >= 1 && inputsRequire(inputs) && regsRequire(regInit))
    val (newOutputs, newRegs) = trans(inputs, regInit)
    if (timeout > 1) {
      c53Run(timeout - 1, inputs, newRegs)
    } else {
      (newOutputs, newRegs)
    }
  }
  def run(inputs: C53Inputs, randomInitValue: C53Regs): (C53Outputs, C53Regs) = {
    require(inputsRequire(inputs) && regsRequire(randomInitValue))
    val regInit = C53Regs()
    c53Run(100, inputs, regInit)
  }
}
