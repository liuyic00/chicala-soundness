package hardware.example.xiangshan

import chisel3._
import chiseltest._
import chiseltest.formal._
import org.scalatest.flatspec.AnyFlatSpec


class DividerSpec extends AnyFlatSpec with Formal with ChiselScalatestTester {
  behavior of "NutCoreFormal"
  it should "pass formal verification" in {

    // verify
    verify(new Divider(8), Seq(BoundedCheck(25), BtormcEngineAnnotation))
  }
}
