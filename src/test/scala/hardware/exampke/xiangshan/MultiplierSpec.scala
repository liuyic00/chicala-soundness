package hardware.example.xiangshan

import chisel3._
import chiseltest._
import chiseltest.formal._
import org.scalatest.flatspec.AnyFlatSpec


class MultiplierSpec extends AnyFlatSpec with Formal with ChiselScalatestTester {
  behavior of "MultiplierSpec"
  it should "pass formal verification" in {

    // verify
    verify(new ArrayMulDataModule(16), Seq(BoundedCheck(1), BtormcEngineAnnotation))
  }
}
