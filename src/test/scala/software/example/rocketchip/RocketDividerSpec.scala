package software.example.rocketchip

import chiseltest._
import hardware.example.rocketchip.{Div => HardwareDivider}
import org.scalatest.flatspec.AnyFlatSpec
import software.util._

class RocketDividerSpec extends AnyFlatSpec with ChiselScalatestTester {
  behavior of "Rocket Divider soft and hard version"

  val lens     = Seq(32, 64)
  val testSize = 1000

  class Hard(dut: HardwareDivider, len: Int, testId: Int) {
    def check(tc: DivTestCase): Unit = {
      // init
      dut.io.req.valid.poke(true)
      dut.io.req.bits.fn.poke(4) // lhs and rhs are signed
      dut.io.req.bits.dw.poke(1) // not sure
      dut.io.req.bits.in1.poke(tc.ua)
      dut.io.req.bits.in2.poke(tc.ub)
      dut.io.req.bits.tag.poke(0)
      dut.io.req.ready.expect(true)
      dut.clock.step()
      // one
      dut.io.req.valid.poke(false)

      def checkUntil(): Unit = {
        if (dut.io.resp.valid.peek().litValue == 1) {
          dut.io.resp.bits.data.expect(tc.uq, s"hard#${testId} ${tc}")
          // dut.io.resp.bits.data.expect(1, s"hard#${testId} ${tc}")
        } else {
          dut.clock.step()
          checkUntil()
        }
      }

      checkUntil()
      // end
      dut.io.resp.ready.poke(true)
      dut.clock.step()
      dut.io.resp.ready.poke(false)
    }
  }

  class Soft(len: Int, testId: Int) {

    import librarySimUInt._

    val soft = Div(w = len)

    def check(tc: DivTestCase): Unit = {
      val inputs = DivInputs(
        Bool(true),          // io_req_valid: Bool,
        UInt(0, log2Up(32)), // io_req_bits_tag: UInt,
        UInt(1, 1),          // io_req_bits_dw: UInt,
        UInt(4, 4),          // io_req_bits_fn: UInt,
        UInt(tc.ua, len),    // io_req_bits_in1: UInt,
        UInt(tc.ub, len),    // io_req_bits_in2: UInt,
        Bool(true)           // io_resp_ready: Bool
      )

      def checkUntil(regs: DivRegs): Unit = {
        val (newOutputs, newRegs) = soft.trans(inputs, regs)
        if (newOutputs.io_resp_valid.value == true) {
          assert(
            newOutputs.io_resp_bits_data.value == tc.uq,
            s"soft#${testId} ${tc}"
          )
        } else
          checkUntil(newRegs)
      }

      val regInit = DivRegs(
        Lit(0, 3).U,                            // state: UInt,
        RandomLibUInt(log2Up(32).toInt),        // req_tag: UInt,
        RandomLibUInt(1),                       // req_dw: UInt,
        RandomLibUInt(4),                       // req_fn: UInt,
        RandomLibUInt(len),                     // req_in1: UInt,
        RandomLibUInt(len),                     // req_in2: UInt,
        RandomLibUInt(log2Ceil(len + 1).toInt), // count: UInt,
        RandomLibUInt(1).asBool,                // neg_out: Bool,
        RandomLibUInt(1).asBool,                // isHi: Bool,
        RandomLibUInt(1).asBool,                // resHi: Bool,
        RandomLibUInt(len + 1),                 // divisor: UInt,
        RandomLibUInt((2 * len) + 2)            // remainder: UInt
      )
      checkUntil(regInit)
    }
  }

  lens.foreach { len =>
    it should s"same in ${len} bits" in {
      test(new HardwareDivider(w = len)).withAnnotations(Seq(WriteVcdAnnotation)) { dut =>
        (1 to testSize).foreach { i =>
          val tc = DivTestCase.randomSInt(len)

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
