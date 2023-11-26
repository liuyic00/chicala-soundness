package software.example.xiangshan

import chiseltest._
import hardware.example.xiangshan.{ArrayMulDataModule => HardwareMultiplier}
import org.scalatest.flatspec.AnyFlatSpec
import software.util._
import treadle.executable.BitsInts

class XiangShanMultiplierSpec extends AnyFlatSpec with ChiselScalatestTester {
  behavior of "Xiangshan Multiplier soft and hard version"

  val lens     = Seq(32, 64)
  val testSize = 1000

  class Hard(dut: HardwareMultiplier, len: Int, testId: Int) {
    def check(tc: MulTestCase): Unit = {
      // init
      dut.io.a.poke(tc.xaBits)
      dut.io.b.poke(tc.xbBits)
      dut.io.result.expect(tc.xcBits, s"hard#${testId} ${tc}")
    }
  }

  class Soft(len: Int, testId: Int) {
    import librarySimUInt._

    val soft = ArrayMulDataModule(len + 1)

    def check(tc: MulTestCase): Unit = {
      val inputs = ArrayMulDataModuleInputs(
        UInt(tc.xaBits, len + 1),     // io_a: UInt,
        UInt(tc.xbBits, len + 1),     // io_b: UInt,
        Seq(Bool(false), Bool(false)) // io_regEnables: Seq[Bool]
      )

      def checkUntil(regs: ArrayMulDataModuleRegs): Unit = {
        val (newOutputs, newRegs) = soft.trans(inputs, regs)
        assert(
          newOutputs.io_result.value == tc.xcBits,
          s"soft#${testId} ${tc}"
        )
      }

      val regInit = ArrayMulDataModuleRegs()
      checkUntil(regInit)
    }
  }

  lens.foreach { len =>
    it should s"same in ${len} bits" in {
      test(new HardwareMultiplier(len + 1)).withAnnotations(Seq(WriteVcdAnnotation)) { dut =>
        (1 to testSize).foreach { i =>
          val tc = MulTestCase.random(len)

          // hardware
          val hard = new Hard(dut, len, i)
          hard.check(tc)

          // software
          val soft = new Soft(len, i)
          soft.check(tc)
        }
      }
    }
  }
}
