package software.example.xiangshan

import chisel3._
import chiseltest._
import org.scalatest.freespec.AnyFreeSpec
import chisel3.experimental.BundleLiterals._

import hardware.example.xiangshan.{Divider => HardwareDivider}
import software.util._

class DividerSpec extends AnyFreeSpec with ChiselScalatestTester {
  "Software Divider should behave consistently with hardware version" in {

    val lens     = Seq(32, 64)
    val testSize = 1000

    class Soft(len: Int) {
      import librarySimUInt._
      val soft = Divider(len)

      def check(tc: DivTestCase): Unit = {
        val inputs = DividerInputs(
          Bool(true),
          Seq(UInt(tc.ua, len), UInt(tc.ub, len)),
          Bool(tc.signed),
          Bool(true)
        )
        def checkUntil(regs: DividerRegs): Unit = {
          val (newOutputs, newRegs) = soft.trans(inputs, regs)
          if (newOutputs.io_out_valid.value == true) {
            assert(
              newOutputs.io_out_bits.value == (tc.ur << len) + tc.uq,
              tc.toString
            )
          } else
            checkUntil(newRegs)
        }
        val regInit = DividerRegs(
          Lit(0, 3).U,
          RandomLibUInt(1 + len * 2),
          RandomLibUInt(1).asBool,
          RandomLibUInt(1).asBool,
          RandomLibUInt(len),
          RandomLibUInt(len + 1),
          Lit(0, bitLength(len)).U
        )
        checkUntil(regInit)
      }
    }
    class Hard(dut: HardwareDivider, len: Int) {
      def check(tc: DivTestCase): Unit = {
        // init
        dut.io.in.valid.poke(true)
        dut.io.in.bits(0).poke(tc.ua)
        dut.io.in.bits(1).poke(tc.ub)
        dut.io.sign.poke(tc.signed)
        dut.io.in.ready.expect(true)
        dut.clock.step()
        // one
        dut.io.in.valid.poke(false)
        def checkUntil(): Unit = {
          if (dut.io.out.valid.peek().litValue == 1) {
            dut.io.out.bits.expect((tc.ur << len) + tc.uq)
          } else {
            dut.clock.step()
            checkUntil()
          }
        }
        checkUntil()
        // end
        dut.io.out.ready.poke(true)
        dut.clock.step()
        dut.io.out.ready.poke(false)
      }
    }

    lens.foreach { len =>
      test(new HardwareDivider(len)).withAnnotations(Seq(WriteVcdAnnotation)) { dut =>
        println("xiangshan divider test")
        print(s"${len} test 0")
        (0 until testSize).foreach { i =>
          val tc = DivTestCase.random(len)
          print(s"\r${len} test ${i + 1}")

          // hardware
          val hard = new Hard(dut, len)
          hard.check(tc)

          // software
          val soft = new Soft(len)
          soft.check(tc)
        }
        print("\n")
      }
    }
  }
}
