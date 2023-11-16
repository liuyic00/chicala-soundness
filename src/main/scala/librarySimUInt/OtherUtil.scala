package librarySimUInt

object range {
  /* Range from start (inclusive) to until (exclusive) */
  def apply(start: BigInt, until: BigInt): List[BigInt] = {
    require(start <= until)
    if (until <= start) Nil else start :: range(start + 1, until)
  } ensuring { (res: List[BigInt]) => res.size == until - start }
}

object max {
  def apply(a: BigInt, b: BigInt): BigInt = {
    if (a > b) a else b
  }
  def apply(ns: List[BigInt]): BigInt = {
    require(ns.size > 0)
    def f(n: BigInt, ns: List[BigInt]): BigInt = {
      require(ns.size >= 0)
      ns match {
        case head :: tail => f(max(n, head), tail)
        case Nil          => n
      }
    }
    f(ns.head, ns.tail)
  }
}

object until {
  def apply(l: BigInt, r: BigInt): List[BigInt] = {
    require(l <= r)
    def f(res: List[BigInt], i: BigInt): List[BigInt] = {
      if (l <= i) f(i :: res, i - 1)
      else res
    }
    f(Nil, r - 1)
  }
}
