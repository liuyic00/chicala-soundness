package hardware

object Elaborate extends App {

  val widths = List(4, 8, 16, 32, 64)
  val topGens = List(
    ("xiangshan_div", new example.xiangshan.Divider(_)),
    ("xiangshan_mul", new example.xiangshan.ArrayMulDataModule(_)),
    ("rocketchip_div", (w: Int) => new example.rocketchip.Div(w)),
    ("rocketchip_mul", (w: Int) => new example.rocketchip.Mul(w))
  )

  def targetDir(name: String, width: Int) = {
    Array("--target-dir", s"test_run_dir/Elaborate/${name}_${width}")
  }

  topGens.foreach { case (name, gen) =>
    widths.foreach { width =>
      (name, width) match {
        case ("xiangshan_mul", 4) =>
        case _ =>
          (new chisel3.stage.ChiselStage)
            .emitSystemVerilog(gen(width), targetDir(name, width))
      }
    }
  }
}
