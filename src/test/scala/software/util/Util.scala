package software.util

import scala.util.Random

/** (a, b, Q, R) a = b * Q + R
  */
case class DivTestCase(a: BigInt, b: BigInt, q: BigInt, r: BigInt, width: Int, signed: Boolean) {
  val ua = if (signed) ToSIntBits(a, width) else a
  val ub = if (signed) ToSIntBits(b, width) else b
  val uq = if (signed) ToSIntBits(q, width) else q
  val ur = if (signed) ToSIntBits(r, width) else r
}

object DivTestCase {
  def random(width: Int): DivTestCase = {
    if (Random.nextInt(2) == 0)
      randomUInt(width)
    else
      randomSInt(width)
  }
  def randomUInt(width: Int): DivTestCase = {
    val a = RandomBigInt(width)
    val b = RandomBigInt(width)
    if (b == 0) {
      val q = (1 << width) - 1
      val r = a
      DivTestCase(a, b, q, r, width, false)
    } else {
      val q = a / b
      val r = a - b * q
      DivTestCase(a, b, q, r, width, false)
    }
  }
  def randomSInt(width: Int): DivTestCase = {
    val a = RandomBigInt.signed(width)
    val b = RandomBigInt.signed(width)
    if (b == 0) {
      val q = (1 << width) - 1
      val r = a
      DivTestCase(a, b, q, r, width, true)
    } else {
      val q = a / b
      val r = a - b * q
      DivTestCase(a, b, q, r, width, true)
    }
  }
}

object RandomBigInt {

  /** Get random BigInt under 1 << n
    *
    * @param n
    */
  def apply(n: Int): BigInt = {
    require(n >= 0)
    var s = ""
    for (i <- 0 until n) {
      s = s + Random.nextInt(2).toString
    }
    return BigInt(s, 2)
  }
  def signed(n: Int): BigInt = {
    require(n >= 0)
    apply(n) - (BigInt(1) << (n - 1))
  }
}

object RandomLibUInt {
  import librarySimUInt._
  def apply(len: Int): UInt = {
    UInt(RandomBigInt(len), len)
  }
}

object ToSIntBits {
  def apply(value: BigInt, width: Int): BigInt = {
    if (value >= 0) value
    else {
      val signBit: BigInt = BigInt(1) << (width - 1)
      var p               = -value
      var ls: List[Int]   = List.empty
      for (i <- 0 until width - 1) {
        ls = (p % 2).toInt :: ls
        p = p / 2
      }
      p = 0
      ls.foreach { x =>
        p = p * 2 + (1 - x)
      }
      (p + 1) % signBit + signBit
    }
  }
}
