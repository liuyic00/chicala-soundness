package librarySimUInt

sealed abstract class Bits {
  def asUInt: UInt
}

case class UInt(val value: BigInt, val width: BigInt) extends Bits {
  require(0 < width)
  require(0 <= value && value < Pow2(width), s"value: ${value}, width: ${width}")

  def apply(idx: BigInt): Bool = {
    require(0 <= idx && idx < width)
    Bool((value / Pow2(idx)) % 2 == 1)
  }
  // def apply(idx: BigInt): UInt = {
  //   require(0 <= idx && idx < width)
  //   UInt((value / Pow2(idx)) % 2, 1)
  // }
  def apply(left: BigInt, right: BigInt): UInt = {
    require(right >= 0)
    require(left >= right)
    UInt((value / Pow2(right)) % Pow2(left - right + 1), left - right + 1)
  } ensuring (res => res.width == left - right + 1 && res.value == (this.value / Pow2(right)) % Pow2(left - right + 1))

  def getWidth: BigInt = width
  def asUInt: UInt     = this
  def asSInt: SInt = {
    val signBit = Pow2(this.width - 1)
    val newValue =
      if (value > signBit)
        -(~UInt(value - signBit - 1, width - 1).value)
      else if (value == signBit)
        -value
      else
        value
    SInt(newValue, width)
  }
  def asBool: Bool = {
    require(width == 1)
    Bool(if (value == 1) true else false)
  }
  def :=(that: Bits): UInt = {
    that match {
      case b: Bool =>
        if (b.value) UInt(1, this.width)
        else UInt(0, this.width)
      case u: UInt =>
        UInt(u.value % Pow2(this.width), this.width)
      case s: SInt =>
        this := s.asUInt
    }
  }

  // Unary

  def unary_- : UInt = {
    UInt(
      if (value == 0) 0 else Pow2(width) - value,
      width
    )
  }
  def unary_~ : UInt = {
    def reverseUInt(u: UInt): UInt = {
      def f(result: BigInt, width: BigInt, bits: BigInt): BigInt = {
        if (width > 0) {
          f(result * 2 + bits % 2, width - 1, bits / 2)
        } else {
          result
        }
      }
      UInt(f(0, u.width, u.value), u.width)
    }
    def reverseFlipUInt(u: UInt): UInt = {
      def f(result: BigInt, width: BigInt, bits: BigInt): BigInt = {
        if (width > 0) {
          f(result * 2 + (bits + 1) % 2, width - 1, bits / 2)
        } else {
          result
        }
      }
      UInt(f(0, u.width, u.value), u.width)
    }
    reverseUInt(reverseFlipUInt(this))
  }

  // Binary

  def +(that: UInt): UInt = {
    val carryed  = this.value + that.value
    val newWidth = if (this.width > that.width) this.width else that.width
    val limt     = Pow2(newWidth)

    Pow2.Pow2Monotone(newWidth, this.width)
    Pow2.Pow2Monotone(newWidth, that.width)
    assert(limt >= this.value)
    assert(limt >= that.value)
    assert(carryed >= 0)
    assert(carryed - limt < limt)

    UInt(
      if (carryed >= limt) carryed - limt else carryed,
      newWidth
    )
  } ensuring (res => res.value == (this.value + that.value) % Pow2(res.width))
  def -(that: UInt): UInt = {
    val carryed  = this.value - that.value
    val newWidth = if (this.width > that.width) this.width else that.width
    val limt     = Pow2(newWidth)

    Pow2.Pow2Monotone(newWidth, this.width)
    Pow2.Pow2Monotone(newWidth, that.width)
    assert(limt >= this.value)
    assert(limt >= that.value)
    assert(carryed <= this.value && carryed >= -that.value)
    assert(carryed <= limt && carryed >= -limt)

    UInt(
      if (carryed < 0) carryed + limt else carryed,
      newWidth
    )
  }
  def *(that: UInt): UInt = {
    UInt(this.value * that.value, this.width + that.width)
  }
  def <<(that: UInt): UInt = {
    assert(that.value <= Pow2(that.width) - 1)

    Pow2.Pow2Monotone(Pow2(that.width) - 1, that.value)
    assert(Pow2(that.value) <= Pow2(Pow2(that.width) - 1))

    assert(this.value < Pow2(this.width))
    assert(Pow2(that.value) <= Pow2(Pow2(that.width) - 1))
    assert(Pow2(this.width) * Pow2(Pow2(that.width) - 1) == Pow2(this.width + Pow2(that.width) - 1))
    assert(this.value * Pow2(that.value) < Pow2(this.width + Pow2(that.width) - 1))

    UInt(this.value * Pow2(that.value), this.width + Pow2(that.width) - 1)
  } ensuring (res => res.value < Pow2(this.width + that.value))
  def <<(x: Int): UInt = {
    UInt(this.value << x, this.width + x)
  }
  def >>(that: UInt): UInt = {
    UInt(this.value / Pow2(that.value), this.width)
  }
  def >>(x: Int): UInt = {
    UInt(this.value >> x, this.width - x)
  }

  def &(that: UInt): UInt = {
    UInt(this.value & that.value, if (this.width > that.width) this.width else that.width)
  }
  def |(that: UInt): UInt = {
    UInt(this.value | that.value, if (this.width > that.width) this.width else that.width)
  }
  def ^(that: UInt): UInt = {
    UInt(this.value ^ that.value, if (this.width > that.width) this.width else that.width)
  }

  // def <<(that: BigInt): UInt = {
  //   UInt(this.value * Pow2(that), this.width + that)
  // }

  // Binary compire
  def ===(that: UInt): Bool = {
    Bool(this.value == that.value)
  } ensuring (res => res.value == (this.value == that.value))
  def =/=(that: UInt): Bool = {
    Bool(this.value != that.value)
  }
  def ===(that: Bool): Bool = {
    require(this.width == BigInt(1))
    Bool(this.value == that.asUInt.value)
  }
  def >=(that: UInt): Bool = {
    Bool(this.value >= that.value)
  }
}

object UInt {
  def empty(width: BigInt): UInt = {
    require(0 < width)
    UInt(BigInt(0), width)
  }
  // def :=(that: UInt): Unit = {
  //   val limt     = Pow2(this.width)
  //   this.value = that.value % limt
  // }
}

case class SInt(val value: BigInt, val width: BigInt) extends Bits {

  def apply(idx: BigInt): Bool = {
    Bool((this.asUInt.value / Pow2(idx)) % 2 == 1)
  }
  def apply(left: BigInt, right: BigInt): UInt = {
    UInt((this.asUInt.value / Pow2(right)) % Pow2(left - right + 1), left - right + 1)
  }

  def *(that: SInt): SInt = {
    SInt(this.value * that.value, this.width + that.width)
  }
  def +(that: SInt): SInt = {
    SInt(this.value + that.value, max(this.width, that.width))
  }
  def >>(that: UInt): SInt = {
    (this.asUInt >> that).asSInt
  }

  def asUInt: UInt = {
    val newValue =
      if (value < 0) {
        val signBit = Pow2(width - 1)
        val tmp     = (~UInt(-value, width).value + 1)
        if (tmp >= signBit) tmp
        else tmp + signBit
      } else
        value
    UInt(newValue, width)
  }
}

case class Bool(val value: Boolean) extends Bits {
  def apply(idx: BigInt): Bool = {
    require(idx == 0)
    this
  }
  def asUInt: UInt = {
    if (value) {
      UInt(1, 1)
    } else {
      UInt(0, 1)
    }
  } ensuring (res => res.width == BigInt(1))
  def asBool: Bool = this

  def asBigInt: BigInt = {
    if (value) {
      BigInt(1)
    } else {
      BigInt(0)
    }
  } ensuring (res => res == this.asUInt.value)

  def :=(that: Bool): Bool = {
    Bool(that.value)
  }

  def unary_! : Bool = {
    Bool(!value)
  }
  def unary_~ : Bool = {
    Bool(!value)
  }

  def &(that: Bool): Bool = {
    Bool(this.value & that.value)
  }
  def |(that: Bool): Bool = {
    Bool(this.value | that.value)
  }
  def ^(that: Bool): Bool = {
    Bool(this.value ^ that.value)
  }
  def &&(that: Bool): Bool = {
    Bool(this.value && that.value)
  }
  def ||(that: Bool): Bool = {
    Bool(this.value || that.value)
  }

  def ===(that: Bool): Bool = {
    Bool(this.value == that.value)
  }

  def =/=(that: Bool): Bool = {
    Bool(this.value != that.value)
  }
}

object Bool {
  def empty(): Bool = {
    Bool(false)
  }
}

case class Lit(value: BigInt, width: BigInt) {
  require(0 < width)
  def U: UInt = UInt(value, width)
  def S: SInt = SInt(value, width)
  def B: Bool = Bool(value != 0)
}

// set the width of 0.U to 1, not bitLength(0)
object Lit {
  def apply(value: BigInt): Lit = {
    if (value == 0) {
      Lit(0, 1)
    } else if (value > 0) {
      Pow2.Pow2BitLength(value)
      Lit(value, bitLength(value))
    } else {
      if (isPow2(-value)) // for "1000" under SInt
        Lit(value, bitLength(-value))
      else
        Lit(value, bitLength(-value) + 1)
    }
  }

  def apply(value: Boolean): Lit = {
    Lit(if (value) 1 else 0, 1)
  } // ensuring(res => res.value == (if (value) 1 else 0) && res.width == 1)

  def apply(s: String): Lit = {
    val base = s.head match {
      case 'b'       => 2
      case 'o'       => 8
      case 'h' | 'x' => 16
    }
    val value = BigInt(s.tail, base)
    Lit(value)
  }
}
