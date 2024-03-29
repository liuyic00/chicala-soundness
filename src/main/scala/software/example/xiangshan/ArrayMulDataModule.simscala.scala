package software
package example.xiangshan

import librarySimUInt._

case class ArrayMulDataModuleInputs(
    io_a: UInt,
    io_b: UInt,
    io_regEnables: Seq[Bool]
)
case class ArrayMulDataModuleOutputs(io_result: UInt)
case class ArrayMulDataModuleRegs()

case class ArrayMulDataModule(len: Int) {
  def inputsRequire(inputs: ArrayMulDataModuleInputs): Boolean = inputs match {
    case ArrayMulDataModuleInputs(io_a, io_b, io_regEnables) =>
      io_a.width == len &&
      io_b.width == len &&
      io_regEnables.length == 2
  }
  def outputsRequire(outputs: ArrayMulDataModuleOutputs): Boolean = outputs match {
    case ArrayMulDataModuleOutputs(io_result) =>
      io_result.width == (2 * len)
  }
  def regsRequire(regs: ArrayMulDataModuleRegs): Boolean = regs match {
    case ArrayMulDataModuleRegs() =>
      true
  }

  def trans(inputs: ArrayMulDataModuleInputs, regs: ArrayMulDataModuleRegs): (ArrayMulDataModuleOutputs, ArrayMulDataModuleRegs) = {
    require(inputsRequire(inputs) && regsRequire(regs))

    // output
    var io_result = UInt.empty((2 * len))

    // body
    def signExt(a: UInt, len: Int): UInt = {
      val aLen = a.width
      val signBit = a((aLen - 1))
      if ((aLen >= len)) a((len - 1), 0) else Cat(Fill((len - aLen), signBit), a)
    }
    val (a, b) = (inputs.io_a, inputs.io_b)
    var b_sext = UInt.empty((len + 1))
    var bx2 = UInt.empty((len + 1))
    var neg_b = UInt.empty((len + 1))
    var neg_bx2 = UInt.empty((len + 1))
    b_sext = b_sext := signExt(b, (len + 1))
    bx2 = bx2 := (b_sext << 1)
    neg_b = neg_b := ~b_sext.asUInt
    neg_bx2 = neg_bx2 := (neg_b << 1)
    var columns: Seq[Seq[Bool]] = Seq.fill((2 * len))(Seq[Nothing]())
    var last_x = Lit(0, 3).U
    Range(0, len, 2).foreach((i: Int) => {
      val x = if ((i == 0)) Cat(a(1, 0), Lit(0, 1).U) else if (((i + 1) == len)) signExt(a(i, (i - 1)), 3) else a((i + 1), (i - 1))
      val pp_temp = MuxLookup(x, Lit(0).U, Seq((Lit(1).U -> b_sext), (Lit(2).U -> b_sext), (Lit(3).U -> bx2), (Lit(4).U -> neg_bx2), (Lit(5).U -> neg_b), (Lit(6).U -> neg_b)))
      val s = pp_temp(len)
      val t = MuxLookup(last_x, Lit(0, 2).U, Seq((Lit(4).U -> Lit(2, 2).U), (Lit(5).U -> Lit(1, 2).U), (Lit(6).U -> Lit(1, 2).U)))
      last_x = x
      val (pp, weight) = if ((i == 0)) (Cat(List(~s, s, s, pp_temp)), 0) else if (((i == (len - 1)) || (i == (len - 1)))) (Cat(List(~s, pp_temp, t)), (i - 2)) else (Cat(List(Lit(1, 1).U, ~s, pp_temp, t)), (i - 2))
      (0 until columns.length).foreach((j: Int) => if (((j >= weight) && (j < (weight + pp.width)))) columns = columns.updated(j, (columns(j) :+ pp((j - weight)))))
    })
    def addOneColumn(col: Seq[Bool], cin: Seq[Bool]): (Seq[Bool], Seq[Bool], Seq[Bool]) = {
      var sum = Seq[Bool]()
      var cout1 = Seq[Bool]()
      var cout2 = Seq[Bool]()
      val cin_1 = if (cin.nonEmpty) Seq(cin.head) else Nil
      val cin_2 = if (cin.nonEmpty) cin.drop(1) else Nil
      var s_1 = Seq[Bool]()
      var c_1_1 = Seq[Bool]()
      var c_1_2 = Seq[Bool]()
      var s_2 = Seq[Bool]()
      var c_2_1 = Seq[Bool]()
      var c_2_2 = Seq[Bool]()
      var tmp1 = (Seq[Bool](), Seq[Bool](), Seq[Bool]())
      var tmp2 = (Seq[Bool](), Seq[Bool](), Seq[Bool]())
      val c22 = example.xiangshan.C22()
      var c22_io_in = Seq.fill(2)(UInt.empty(1))
      var c22_io_out = Seq.fill(2)(UInt.empty(1))
      val c32 = example.xiangshan.C32()
      var c32_io_in = Seq.fill(3)(UInt.empty(1))
      var c32_io_out = Seq.fill(2)(UInt.empty(1))
      val c53 = example.xiangshan.C53()
      var c53_io_in = Seq.fill(5)(UInt.empty(1))
      var c53_io_out = Seq.fill(3)(UInt.empty(1))
      if ((col.size == 1)) sum = (col ++ cin) else if ((col.size == 2)) {
        (0 until c22_io_in.length)
          .zip(col)
          .foreach { case (i, s) => c22_io_in = c22_io_in.updated[UInt, Seq[UInt]](i, c22_io_in(i) := s)}
        val (t$c22TransOutputs, _) = c22.trans(
          example.xiangshan.C22Inputs(c22_io_in),
          example.xiangshan.C22Regs()
        )
        c22_io_out = t$c22TransOutputs.io_out
        sum = {
          val rassoc$1 = c22_io_out(0).asBool
          (rassoc$1 +: cin)
        }
        cout2 = Seq(c22_io_out(1).asBool)
      } else if ((col.size == 3)) {
        (0 until c32_io_in.length)
          .zip(col)
          .foreach { case (i, s) => c32_io_in = c32_io_in.updated[UInt, Seq[UInt]](i, c32_io_in(i) := s)}
        val (t$c32TransOutputs, _) = c32.trans(
          example.xiangshan.C32Inputs(c32_io_in),
          example.xiangshan.C32Regs()
        )
        c32_io_out = t$c32TransOutputs.io_out
        sum = {
          val rassoc$2 = c32_io_out(0).asBool
          (rassoc$2 +: cin)
        }
        cout2 = Seq(c32_io_out(1).asBool)
      } else if ((col.size == 4)) {
        (0 until c53_io_in.length)
          .zip((col.take(4) :+ (if (cin.nonEmpty) cin.head else Lit(0).U)))
          .foreach { case (i, s) => c53_io_in = c53_io_in.updated[UInt, Seq[UInt]](i, c53_io_in(i) := s)}
        val (t$c53TransOutputs, _) = c53.trans(
          example.xiangshan.C53Inputs(c53_io_in),
          example.xiangshan.C53Regs()
        )
        c53_io_out = t$c53TransOutputs.io_out
        sum = (Seq(c53_io_out(0).asBool) ++ (if (cin.nonEmpty) cin.drop(1) else Nil))
        cout1 = Seq(c53_io_out(1).asBool)
        cout2 = Seq(c53_io_out(2).asBool)
      } else {
        tmp1 = addOneColumn(col.take(4), cin_1)
        tmp2 = addOneColumn(col.drop(4), cin_2)
        s_1 = tmp1._1
        c_1_1 = tmp1._2
        c_1_2 = tmp1._3
        s_2 = tmp2._1
        c_2_1 = tmp2._2
        c_2_2 = tmp2._3
        sum = (s_1 ++ s_2)
        cout1 = (c_1_1 ++ c_2_1)
        cout2 = (c_1_2 ++ c_2_2)
      }
      (sum, cout1, cout2)
    }
    def addAll(cols: Seq[Seq[Bool]], depth: Int): (UInt, UInt) = {
      var k = 0
      var columns_next = Seq.fill((2 * len))(Seq[Bool]())
      var cout1 = Seq[Bool]()
      var cout2 = Seq[Bool]()
      if (cols.forall((x$7: Seq[Bool]) => (x$7.size <= 2))) {
        (0 until cols.size).foreach((i: Int) => if ((cols(i).size == 1)) k = (i + 1))
        (Cat(cols.map((x$8: Seq[Bool]) => x$8(0)).reverse), Cat(Cat(cols.drop(k).map((x$9: Seq[Bool]) => x$9(1)).reverse), Lit(0, k).U))
      } else {
        (0 until cols.length).foreach((i: Int) => {
          val (s, c1, c2) = addOneColumn(cols(i), cout1)
          columns_next = columns_next.updated(i, (s ++ cout2))
          cout1 = c1
          cout2 = c2
        })
        addAll(columns_next, (depth + 1))
      }
    }
    val (sum, carry) = addAll(columns, 0)
    io_result = io_result := (sum + carry)

    (
      ArrayMulDataModuleOutputs(io_result),
      ArrayMulDataModuleRegs()
    )
  }

  def arrayMulDataModuleRun(timeout: Int, inputs: ArrayMulDataModuleInputs, regInit: ArrayMulDataModuleRegs): (ArrayMulDataModuleOutputs, ArrayMulDataModuleRegs) = {
    require(timeout >= 1 && inputsRequire(inputs) && regsRequire(regInit))
    val (newOutputs, newRegs) = trans(inputs, regInit)
    if (timeout > 1) {
      arrayMulDataModuleRun(timeout - 1, inputs, newRegs)
    } else {
      (newOutputs, newRegs)
    }
  }
  def run(inputs: ArrayMulDataModuleInputs, randomInitValue: ArrayMulDataModuleRegs): (ArrayMulDataModuleOutputs, ArrayMulDataModuleRegs) = {
    require(inputsRequire(inputs) && regsRequire(randomInitValue))
    val regInit = ArrayMulDataModuleRegs()
    arrayMulDataModuleRun(100, inputs, regInit)
  }
}
