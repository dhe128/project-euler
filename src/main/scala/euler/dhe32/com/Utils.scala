package euler.dhe32.com
import scala.collection._
import Implicits._
import scalaz.{ Ordering => _, _ }
import spire.algebra._
import spire.math._
import spire.implicits._
import spire.syntax.literals._
import spire.syntax.literals.si._
import scala.util.DynamicVariable
import scala.collection.generic.CanBuildFrom
import scala.language.higherKinds
import scala.{ specialized => spec }

object Utils {
  def tau = 2.0 * pi

  def getResource(name: String) =
    io.Source.fromURL(getClass.getResource("resources/" + name))

  def factor[T: Integral](n: T): List[T] = {
    val integral = implicitly[Integral[T]]
    import integral._

    def f(n: T, k: T): List[T] = {
      if (k * k > n)
        n :: Nil
      else if (n % k == 0)
        k :: f(n /~ k, k)
      else
        f(n, k + one)
    }
    if (n == 1)
      Nil
    else
      f(n, (one + one))
  }

  def factor2[T: Integral](n: T) = {
    def group(fs: List[T]): List[(T, Int)] = fs match {
      case hd :: Nil =>
        (hd, 1) :: Nil
      case hd :: tl =>
        val (f, k) :: ys = group(tl)
        if (hd == f)
          (hd, k + 1) :: ys
        else
          (hd, 1) :: (f, k) :: ys
      case Nil => Nil
    }
    group(factor(n))
  }

  def factorIterator[T: Integral](_n: T): Iterator[T] =
    new Iterator[T] {
      val integral = implicitly[Integral[T]]
      import integral._

      var n = _n
      var k = fromInt(2)
      def hasNext = {
        while (n % k != 0) {
          k += 1
          if (k * k > n)
            k = n
        }
        n != 1
      }

      def next =
        if (hasNext) {
          n /~= k
          k
        } else
          Iterator.empty.next
    }

  def isPrime[T: Integral](n: T) = {
    val integral = implicitly[Integral[T]]
    import integral._

    if (n <= one)
      false
    else {
      val factor = (2 to isqrt(n).toInt) find (n % fromInt(_) == 0)
      factor.isEmpty
    }
  }

  def divisors[T: Integral](fs: List[(T, Int)]): Iterator[T] = {
    val integral = implicitly[Integral[T]]
    import integral._

    fs match {
      case (p, k) :: tl => for {
        j <- (0 to k).iterator
        y <- divisors(tl)
      } yield (p ** j) * y
      case Nil => Iterator single one
    }
  }
  def numDivisors[T: Integral](n: T): T = sigma(n, 0)
  def sigma[T: Integral](n: T): T = sigma(n, 1)

  def sigma[T: Integral](n: T, k: Int): T =
    sigma(factor2(n), k)

  def sigma[T: Integral](fs: List[(T, Int)], k: Int): T = {
    val integral = implicitly[Integral[T]]
    import integral._
    if (k == 0)
      (fs map { case (_, a) => fromInt(a + 1) }).qproduct
    else
      (fs map { case (p, a) => (p ** (k * (a + 1)) - one) /~ (p ** k - one) }).qproduct
  }

  def sigmaProper(n: BigInt, k: Int): BigInt =
    sigma(n, k) - (n pow k)

  def phi[T: Integral](n: T): T = {
    val integral = implicitly[Integral[T]]
    import integral._
    val ps = factor2(n) map (_._1)
    (n /: ps)((n, p) => n /~ p * (p - one))
  }

  def carmichael(x: Int) = {
    val fs = factor2(x)
    (fs map { case (p, k) => (p - 1) * (p ** (k - 1)) }).product
  }

  /*
  def gcd[T: Integral](a: T, b: T): T = {
    val integral = implicitly[Integral[T]]
    import integral._
    if (b == 0)
      abs(a)
    else
      Utils.gcd(b, divide(a, b)._2)
  }
*/

  def euclid[T: Integral](a: T, b: T): (T, T, T) = {
    val integral = implicitly[Integral[T]]
    import integral._

    ((Iterator iterate ((one, zero, a), (zero, one, b))) {
      case ((s_, t_, a), (s, t, b)) =>
        val (q, r) = a /% b
        ((s, t, b), (s_ - q * s, t_ - q * t, r))
    } find (_._2._3 == 0)).get._1
  }

  def lcm[T: Integral](a: T, b: T): T = {
    val integral = implicitly[Integral[T]]
    import integral._
    a /~ gcd(a, b) * b
  }

  def inverseMonotonic(f: Double => Double, range: (Double, Double) = (-1e10, 1e10)): Double => Double = {
    def finv(x: Double): Double = {
      def binsearch(a: Double, b: Double): Double = {
        if (b - a < 1e-10)
          a
        else {
          val c = a + 0.5 * (b - a)
          if (f(c) < x)
            binsearch(c, b)
          else
            binsearch(a, c)
        }
      }
      binsearch(range._1, range._2)
    }
    finv
  }

  def collatz[T: Integral](n: T) = {
    val integral = implicitly[Integral[T]]
    import integral._

    val (q, r) = n /% fromInt(2)
    if (r == 0)
      q
    else
      fromInt(3) * n + one
  }

  def primes(N: Int) = {
    val xs = mutable.BitSet(N)
    val n2 = isqrtCeil(N)

    val it1 = new Iterator[Int] {
      var x = 2
      def hasNext = x < n2
      def next = {
        val y = x
        var c = x + x
        while (c < N) {
          xs += c
          c += x
        }

        x += 1
        while (x < n2 && xs(x)) x += 1
        y
      }
    }

    lazy val it2 = (n2 until N).iterator filter (!xs(_))
    it1 ++ it2
  }

  def primesRange(u: Long, v: Long) = {
    val v2 = isqrt(v).toInt
    val ps = primes(v2)
    val xs = LongBitSet(v - u)

    ps foreach { p =>
      var c = u - u % p + p
      while (c < v) {
        xs add (c - u)
        c += p
      }
    }

    (0L until (v - u)).iterator filter (x => !(xs get x)) map (_ + u)
  }

  def npr(n: Int, k: Int) =
    (BigInt(n - k + 1) to n).product

  def ncr(n: Int, k: Int) =
    (BigInt(k + 1) to n).product / (BigInt(1) to (n - k)).product

  def nc2[T: Integral](n: T) = {
    val integral = implicitly[Integral[T]]
    import integral._
    n * (n - one) /~ (one + one)
  }

  def nc2Invi(x: BigInt) =
    (isqrt(1 + 8 * x) - 1) / 2

  lazy val factorial = memoizeY((n: Int, factorial: Int => BigInt) => {
    if (n == 0)
      BigInt(1)
    else
      factorial(n - 1) * n
  })

  def multinomial(xs: List[Int]) =
    factorial(xs.sum) / (xs map factorial).product

  def lexico(n: BigInt, k: Int): List[Int] = {
    if (k == 1)
      0 :: Nil
    else {
      val (q_, r) = n /% factorial(k - 1)
      val q = q_.toInt
      q :: (lexico(r, k - 1) map { x => if (x < q) x else x + 1 })
    }
  }

  // n-tuples of non-negative integers which sum to k
  // length is ncr(n + k - 1, k)
  def starsAndBars(n: Int, k: Int): Iterator[List[Int]] = {
    if (n == 0 && k == 0)
      Iterator single Nil
    else if (n == 0)
      Iterator.empty
    else if (n == 1)
      Iterator single k :: Nil
    else
      for {
        a <- (0 to k).iterator
        bs <- starsAndBars(n - 1, k - a)
      } yield a :: bs
  }

  lazy val fibonacci = memoizeY((n: Int, fibonacci: Int => BigInt) => {
    n match {
      case 0 => BigInt(0)
      case 1 => BigInt(1)
      case _ if n > 0 => fibonacci(n - 1) + fibonacci(n - 2)
      case _ => (-1) ** (-n + 1) * fibonacci(-n)
    }
  })

  val fibonacciIterator: Iterator[BigInt] = {
    (Iterator iterate (BigInt(1), BigInt(0))) {
      case (a, b) => (b, a + b)
    } map (_._2)
  }

  def fromBigInt[T: Integral](a: BigInt): T = {
    val integral = implicitly[Integral[T]]
    import integral._
    (integral.one match {
      case (_: Byte) => a.toByte
      case (_: Char) => a.toChar
      case (_: Short) => a.toShort
      case (_: Int) => a.toInt
      case (_: Long) => a.toLong
      case (_: BigInt) => a
    }).asInstanceOf[T]
  }

  def splitBase[T: Integral](base: Int, x: T) =
    splitBaseLe(base, x).reverse

  def splitBaseLe[T: Integral](base: Int, x: T) = {
    val integral = implicitly[Integral[T]]
    import integral._
    def rec(x: T): List[Int] =
      if (x == zero)
        Nil
      else {
        val (q, r) = x /% fromInt(base)
        r.toInt :: rec(q)
      }
    rec(x)
  }

  def joinBase[T: Integral](base: Int, xs: Seq[Int]): T = {
    val integral = implicitly[Integral[T]]
    import integral._
    (zero /: xs) {
      case (s, x) => fromInt(x) + s * fromInt(base)
    }
  }

  def split10(x: Int) = splitBase(10, x)
  def split10(x: BigInt) = splitBase(10, x)
  def split10[T: Integral](x: T) = splitBase(10, x)
  def join10(xs: Seq[Int]) = joinBase[Int](10, xs)

  def ilog[T: Integral](b: Int, x: T): Int = {
    val integral = implicitly[Integral[T]]
    import integral._
    if (x == 0) -1 else ilog(b, x /~ fromInt(b)) + 1
  }

  def ilog10[T: Integral](x: T): Int = ilog(10, x)
  def isqrt[T: Integral](x: T): T = {
    val integral = implicitly[Integral[T]]
    import integral._

    (one match {
      case (_: BigInt) => fromType(sqrt(toNumber(x)))
      case (_: Long) =>
        if (x < 0)
          throw new Exception("Must be non-negative")
        var y = Math.floor(Math.sqrt(x.toDouble)).toLong
        while (y * y > x) y -= 1
        while ((y + 1) * (y + 1) <= x) y += 1
        y
      case _ => fromInt(Math.floor(Math.sqrt(x.toDouble)).toInt)
    }).asInstanceOf[T]

  }

  def isqrtCeil[T: Integral](x: T): T = {
    val integral = implicitly[Integral[T]]
    import integral._
    (integral.one match {
      case (_: BigInt) => BigDecimalMath.sqrt(x.toBigDecimal).setScale(0, BigDecimal.RoundingMode.CEILING).toBigInt
      case (_: Long) => Math.ceil(x.toDouble).toLong
      case _ => fromInt(Math.ceil(Math.sqrt(x.toDouble)).toInt)
    }).asInstanceOf[T]
  }

  def isSquare[T: Integral](x: T) =
    isqrt(x) ** 2 == x

  /*
  def ipow[T: Integral](b: T, k: T): T = {
    val integral = implicitly[Integral[T]]
    import integral._
    if (k == 0)
      one
    else {
      val (q, r) = k /% (one + one)
      val s = ipow(b, q)
      s * s * (if (r == 1) b else one)
    }
  }
  */

  def genExp[A, T: Integral](op: (A, A) => A)(a: A, k: T): A = {
    val integral = implicitly[Integral[T]]
    import integral._
    if (k == 1)
      a
    else {
      val (q, r) = k /% (one + one)
      val s = genExp(op)(a, q)
      val s2 = op(s, s)
      if (r == 1)
        op(s2, a)
      else
        s2
    }
  }

  def powmod[T: Integral](b: T, k: T, n: T): T = {
    val integral = implicitly[Integral[T]]
    import integral._

    val f = powmodCached(b, n)
    f(k)
  }

  def powmodCached[T: Integral](b: T, n: T): T => T = {
    val integral = implicitly[Integral[T]]
    import integral._

    memoizeY(
      (k: T, f: T => T) =>
        if (k == 0)
          one % n
        else {
          val (q, r) = k /% (one + one)
          val s = f(q)
          val x = (s * s) % n
          if (r == 0) x else (x * b) % n
        })
  }

  def leastUpperBound[T: Ordering](xs: Int => T,
    a: Int = Int.MinValue, b: Int = Int.MaxValue)(t: T): Int = {
    val compare = implicitly[Ordering[T]].compare _

    def rec(a: Int, b: Int): Int = {
      if (a == b) a
      else if (a + 1 == b) {
        if (compare(t, xs(a)) <= 0) a else b
      } else {
        val mid = a + (b - a) / 2;
        if (compare(t, xs(mid)) <= 0)
          rec(a, mid);
        else
          rec(mid, b);
      }
    }
    rec(a, b)
  }

  def leastStrictUpperBound[T: Ordering](xs: Int => T,
    a: Int = Int.MinValue, b: Int = Int.MaxValue)(t: T): Int = {
    val compare = implicitly[Ordering[T]].compare _

    def rec(a: Int, b: Int): Int = {
      if (a == b) a
      else if (a + 1 == b) {
        if (compare(t, xs(a)) < 0) a else b
      } else {
        val mid = a + (b - a) / 2;
        if (compare(t, xs(mid)) < 0)
          rec(a, mid);
        else
          rec(mid, b);
      }
    }
    rec(a, b)
  }

  def greatestLowerBound[T: Ordering](xs: Int => T,
    a: Int = Int.MinValue, b: Int = Int.MaxValue)(t: T) =
    leastStrictUpperBound(xs, a, b)(t) - 1

  def greatestStrictLowerBound[T: Ordering](xs: Int => T,
    a: Int = Int.MinValue, b: Int = Int.MaxValue)(t: T) =
    leastUpperBound(xs, a, b)(t) - 1

  def leastUpperBoundLong[T: Ordering](xs: Long => T,
    a: Long = Long.MinValue, b: Long = Long.MaxValue)(t: T): Long = {
    val compare = implicitly[Ordering[T]].compare _

    def rec(a: Long, b: Long): Long = {
      if (a == b) a
      else if (a + 1 == b) {
        if (compare(t, xs(a)) <= 0) a else b
      } else {
        val mid = a + (b - a) / 2;
        if (compare(t, xs(mid)) <= 0)
          rec(a, mid);
        else
          rec(mid, b);
      }
    }
    rec(a, b)
  }

  def leastStrictUpperBoundLong[T: Ordering](xs: Long => T,
    a: Long = Long.MinValue, b: Long = Long.MaxValue)(t: T): Long = {
    val compare = implicitly[Ordering[T]].compare _

    def rec(a: Long, b: Long): Long = {
      if (a == b) a
      else if (a + 1 == b) {
        if (compare(t, xs(a)) < 0) a else b
      } else {
        val mid = a + (b - a) / 2;
        if (compare(t, xs(mid)) < 0)
          rec(a, mid);
        else
          rec(mid, b);
      }
    }
    rec(a, b)
  }

  def greatestLowerBoundLong[T: Ordering](xs: Long => T,
    a: Long = Long.MinValue, b: Long = Long.MaxValue)(t: T) =
    leastStrictUpperBoundLong(xs, a, b)(t) - 1

  def greatestStrictLowerBoundLong[T: Ordering](xs: Long => T,
    a: Long = Long.MinValue, b: Long = Long.MaxValue)(t: T) =
    leastUpperBoundLong(xs, a, b)(t) - 1

  def binarySearch[T: Ordering](xs: IndexedSeq[T], t: T) = {
    val ix = greatestLowerBound(xs, 0, xs.length)(t)
    ix != -1 && xs(ix) == t
  }

  // little endian
  def ndIndex(xs: List[Int]): Iterator[List[Int]] =
    xs match {
      case Nil => Iterator single Nil
      case hd :: tl =>
        for {
          zs <- ndIndex(tl)
          y <- (0 until hd).iterator
        } yield y :: zs
    }

  // big endian
  def ndIndexBe(xs: List[Int], reverse: Boolean = false): Iterator[List[Int]] =
    xs match {
      case Nil => Iterator single Nil
      case hd :: tl =>
        val ys = 0 until hd
        for {
          y <- if (reverse) ys.reverse.iterator else ys.iterator
          zs <- ndIndex(tl)
        } yield y :: zs
    }

  // big endian
  def ndIndexFrom(xs: List[Int], as: List[Int]): Iterator[List[Int]] =
    ndIndexTo(xs, as, xs map (_ - 1))

  // big endian, inclusive at endpoints
  def ndIndexTo(xs: List[Int], as: List[Int], bs: List[Int], reverse: Boolean = false): Iterator[List[Int]] =
    xs match {
      case Nil => Iterator single Nil
      case hd :: tl =>
        val ys = Math.max(as.head, 0) to Math.min(bs.head, hd - 1)
        for {
          y <- if (reverse) ys.reverse.iterator else ys.iterator
          zs <- if (y == as.head && y == bs.head)
            ndIndexTo(tl, as.tail, bs.tail, reverse)
          else if (y == as.head)
            ndIndexTo(tl, as.tail, tl map (_ - 1), reverse)
          else if (y == bs.head)
            ndIndexTo(tl, (List fill tl.length)(0), bs.tail, reverse)
          else
            ndIndexBe(tl, reverse)
        } yield y :: zs
    }

  // big endian, inclusive at bottom, exclusive at top
  /*
  def ndIndexUntil(xs: List[Int], as: List[Int], bs: List[Int]): Iterator[List[Int]] =
    xs match {
      case Nil => Iterator single Nil
      case hd :: Nil =>
        (as.head until bs.head).iterator map (_ :: Nil)
      case hd :: tl =>
        for {
          y <- (Math.max(as.head, 0) to Math.min(bs.head, hd)).iterator
          zs <- if (y == as.head || y == bs.head)
            ndIndexUntil(tl, as.tail, bs.tail)
          else
            ndIndex(tl)
        } yield y :: zs
    }
    * 
    */

  def tune[B](a: Double = 1.0, base: Double = 2.0)(f: Double => Option[B]) = {
    val r = for {
      m <- Iterator from 0 map (a * Math.pow(base, _))
      r <- f(m)
    } yield r
    r.next
  }

  def tunel[B](a: Long = 1, base: Long = 2)(f: Long => Option[B]) = {
    val r = for {
      m <- Iterator from 0 map (e => a * (base ** e))
      r <- f(m)
    } yield r
    r.next
  }

  def memoize[A, B](f: A => B) = {
    val M = mutable.Map.empty[A, B]
    a: A => M getOrElseUpdate (a, f(a))
  }

  def memoizeThreadLocal[A, B](f: A => B) = {
    val M = new DynamicVariable(mutable.Map.empty[A, B])
    a: A => M.value getOrElseUpdate (a, f(a))
  }

  def memoizeY[A, B](f: (A, A => B) => B) = {
    var yf: A => B = null
    yf = memoize(f(_, yf(_)))
    yf
  }

  def Y[A, B](f: (A, A => B) => B) = {
    var yf: A => B = null
    yf = f(_, yf(_))
    yf
  }

  def cfEval[T: Integral](ks: Iterator[T]) = {
    var x2 = (BigInt(0), BigInt(1))
    var x1 = (BigInt(1), BigInt(0))
    ks map { k =>
      val y = (k.toBigInt * x1._1 + x2._1, k.toBigInt * x1._2 + x2._2)
      x2 = x1
      x1 = y
      y
    }
  }

  def cfEvalWithSemiConvergents[T: Integral](ks: Iterator[T]) = {
    var x2 = (BigInt(0), BigInt(1))
    var x1 = (BigInt(1), BigInt(0))
    ks map { k =>
      val ys = ((1 until k.toInt) :+ k.toInt) map (a => (a * x1._1 + x2._1, a * x1._2 + x2._2))
      x2 = x1
      x1 = ys.last
      ys.toList
    }
  }

  def sqrtCf(x: Long) = {
    val k = isqrt(x)
    (Iterator iterate (k, (x, k, 1L))) {
      case (_, (a, b, c)) =>
        val k = Math.floor(c.toDouble / (Math.sqrt(a) - b)).toLong
        val d = (a - b * b) / c
        val y = (a, k * d - b, d)
        (k, y)
    }
  }

  def rationalCf[T: Integral](a0: T, b0: T) = {
    object it extends Iterator[T] {
      var a = a0
      var b = b0
      def hasNext = b != 0
      def next = {
        val (q, r) = divide(a, b)
        a = b
        b = r
        q
      }
    }
    it
  }

  def iterateState[S, A](m: State[S, A], s0: S) = {
    var s = s0
    new Iterator[A] {
      def hasNext = true
      def next = {
        val (s2, a) = m(s)
        s = s2
        a
      }
    }
  }

  def divide[T: Integral](n: T, d: T) = {
    val integral = implicitly[Integral[T]]
    import integral._

    var (q, r) = n /% d
    val dSign = if (d > zero) one else -one
    if (r < zero) {
      r += dSign * d
      q -= dSign
    }
    (q, r)
  }

  def ngon(p: Int)(n: Int) = ((p - 2) * n * n - (p - 4) * n) / 2

  lazy val pfn = memoizeY((n: Int, pfn: Int => BigInt) => {
    def term(k2: Int) = {
      val k = if (k2 % 2 == 1)
        (k2 + 1) / 2
      else
        -(k2 + 1) / 2
      val sign = if (divide(k, 2)._2 == 1) 1 else -1
      val arg = n - ngon(5)(k)
      (sign, arg)
    }

    if (n == 0)
      BigInt(1)
    else {
      val xs = Iterator from 1 map term takeWhile (_._2 >= 0) map { case (sign, arg) => sign * pfn(arg) }
      xs.sum
    }
  })

  def catalan(n: Int) = ncr(2 * n, n) / (n + 1)

  lazy val integerPartition_ = memoizeY((ny: (Int, Int), p: Tuple2[Int, Int] => List[List[Int]]) => {
    val (n, y) = ny
    if (n == 0)
      Nil
    else if (y == 1)
      (List fill n)(y) :: Nil
    else
      (if (n == y) List(n :: Nil) else Nil) ::: ((0 to (n / y)).toList.reverse flatMap { k => p((n - k * y, y - 1)) map { (List fill k)(y) ::: _ } })
  })

  def integerPartition(n: Int) =
    integerPartition_(n, n)

  def dijkstra[T: Ordering](G: T => TraversableOnce[T], source: T, weight: (T, T) => Int): (Map[T, Int], Map[T, T]) = {
    val dist = mutable.Map.empty[T, Int] withDefault (_ => Int.MaxValue)
    val Q = mutable.SortedSet.empty(Ordering by { (x: T) => (dist(x), x) })
    val prev = mutable.Map.empty[T, T]

    dist(source) = 0
    Q += source
    while (!Q.isEmpty) {
      val u = Q.head
      Q -= u

      for (v <- G(u)) {
        val alt = dist(u) + weight(u, v)
        if (alt < dist(v)) {
          Q -= v
          dist(v) = alt
          prev(v) = u
          Q += v
        }
      }
    }

    (dist, prev)
  }

  def prim[T: Ordering](G: T => TraversableOnce[T], source: T, weight: (T, T) => Int) = {
    val dist = mutable.Map.empty[T, Int] withDefault (_ => Int.MaxValue)
    val Q = mutable.SortedSet.empty(Ordering by { (x: T) => (dist(x), x) })
    val prev = mutable.Map.empty[T, T]
    val visited = mutable.Set.empty[T]

    Q += source
    while (!Q.isEmpty) {
      val u = Q.head
      Q -= u
      visited += u

      for (v <- G(u)) {
        val alt = weight(u, v)
        if (!(visited contains v) && alt < dist(v)) {
          Q -= v
          dist(v) = alt
          prev(v) = u
          Q += v
        }
      }
    }
    prev
  }

  object Permutation {
    def cauchy[T](xs: Seq[T], ys: Seq[T]) = {
      val M = xs.zipWithIndex.reverse.toMap
      ys.toList map M
    }
  }

  def lagrangeInterpolation(xys: Seq[(Double, Double)]) = {
    val (xs, ys) = xys.unzip

    def lagrange(j: Int)(x: Double) = {
      val xj = xs(j)
      val ps = xs.zipWithIndex filterNot (_._2 == j) map {
        case (xm, m) => (x - xm) / (xj - xm)
      }
      ps.product
    }

    (x: Double) => {
      val ts = ys.zipWithIndex map { case (y, j) => y * lagrange(j)(x) }
      ts.sum
    }
  }

  // Bell numbers: 1, 1, 2, 5, 15, 52, ...
  lazy val bell = memoizeY((n: Int, f: Int => BigInt) =>
    if (n == 0)
      BigInt(1)
    else
      ((0 to (n - 1)) map (k => ncr(n - 1, k) * f(k))).sum)

  // Partitions of the set 0, 1, ..., n - 1
  lazy val setPartitions = memoizeY((n: Int, f: Int => List[List[List[Int]]]) =>
    if (n == 0)
      Nil :: Nil
    else if (n == 1)
      ((0 :: Nil) :: Nil) :: Nil
    else
      for {
        k <- (0 to (n - 1)).toList
        as <- (1 until n).toList combinations k map (0 :: _)
        g = (1 until n filterNot (as contains _)).toIndexedSeq
        css <- f(n - 1 - k)
      } yield as :: (css map (_ map g.apply)))

  // 
  def multisetPartitions(xs: List[Int]) = {
    def f(xs: List[Int], vs: List[Int]): Iterator[List[List[Int]]] =
      if (xs.sum == 0)
        Iterator single Nil
      else
        for {
          as <- ndIndexTo(xs map (_ + 1), (List fill xs.length)(0), vs) drop 1
          asLin = as.zipWithIndex flatMap { case (k, a) => (List fill k)(a) }
          bs = xs zip as map (z => z._1 - z._2)
          css <- f(bs, as)
        } yield asLin :: css

    f(xs, xs)
  }

  // A bit set that can store more than 2^31 elements
  case class LongBitSet(size: Long) {
    def arrayLength = 1 << 16
    def wordSize = 1 << 6
    def arrayCapacity = arrayLength * wordSize

    val data = (Array fill (size / arrayCapacity + 1).toInt)(new Array[Long](arrayLength))

    def set(x: Long, y: Boolean) = {
      val q = (x / arrayCapacity).toInt
      val r = x % arrayCapacity
      val arr = data(q)
      val a = (r / wordSize).toInt
      val b = r % wordSize
      arr(a) =
        if (y)
          arr(a) | (1L << b)
        else
          arr(a) & ~(1L << b)
    }

    def get(x: Long) = {
      val q = (x / arrayCapacity).toInt
      val r = x % arrayCapacity
      val arr = data(q)
      val a = (r / wordSize).toInt
      val b = r % wordSize
      (arr(a) & (1L << b)) != 0L
    }

    def add(x: Long) = set(x, true)
    def remove(x: Long) = set(x, false)
  }

  // supports primes over 2^31
  def longPrimesRaw(n: Long) = {
    val xs = LongBitSet(n)
    xs set (0, true)
    xs set (1, true)

    for (x <- 2L until isqrtCeil(n))
      if (!(xs get x)) {
        var c = x + x
        while (c < n) {
          xs add c
          c += x
        }
      }
    xs
  }

  def pnt(x: Double) = x / Math.log(x)
  def pntInv(x: Double) = x * Math.log(x)

  def centerHex(x: Int) = BigInt(3) * x * (x - 1) + 1

  def fromHex(p: (Int, Int)): Int = {
    val (x, y) = p

    if ((x, y) == (0, 0))
      0
    else {
      val (q, r, t) =
        if (x >= 0 && y >= 0 && y <= x)
          (0, x, y)
        else if (x >= 0 && y >= 0 && x < y)
          (1, y, y - x)
        else if (x <= 0 && y >= 0)
          (2, -x + y, -x)
        else if (x <= 0 && y <= 0 && x <= y)
          (3, -x, -y)
        else if (x <= 0 && y <= 0 && y < x)
          (4, -y, -y + x)
        else
          (5, x - y, x)

      centerHex(r).toInt + r * q + t
    }
  }

  def toHex(x: Int): (Int, Int) = {
    def centerHexInv(x: Int) = greatestLowerBound(centerHex, 0)(x)
    val r = centerHexInv(x)
    if (r == -1)
      (0, 0)
    else {
      val (q, t) = divide(x - centerHex(r).toInt, r)

      q match {
        case 0 => (r, t)
        case 1 => (r - t, r)
        case 2 => (-t, r - t)
        case 3 => (-r, -t)
        case 4 => (-r + t, -r)
        case 5 => (t, -r + t)
      }
    }
  }

  def pell(D: Long) =
    (cfEval(sqrtCf(D) map { _._1 }) find { case (x, y) => x * x - D * y * y == 1 }).get

  def negPell(D: Long) =
    (cfEval(sqrtCf(D) map { _._1 }) find { case (x, y) => x * x - D * y * y == -1 }).get

  def pellIterator(D: Long): Iterator[(BigInt, BigInt)] =
    pellIterator(D, pell(D))

  def pellIterator(D: Long, xy0: (BigInt, BigInt)) =
    (Iterator iterate xy0) { pellAdd(D, xy0, _) }

  def pellAdd(D: Long, xy0: (BigInt, BigInt), xy1: (BigInt, BigInt)) = {
    val (x0, y0) = xy0
    val (x1, y1) = xy1
    (x0 * x1 + D * y0 * y1, x0 * y1 + x1 * y0)
  }

  def pellEquiv(D: Long, N: BigInt, xy0: (BigInt, BigInt), xy1: (BigInt, BigInt)) = {
    val xy2 = pellAdd(D, xy0, (-xy1._1, xy1._2))
    (xy2._1 % N == 0) && (xy2._2 % N == 0)
  }

  def generalPellIterator(D: Long, c: BigInt): Iterator[(BigInt, BigInt)] =
    generalPellIterator(D, generalPell(D, c))

  def generalPellIterator(D: Long, fxys: Seq[(BigInt, BigInt)]): Iterator[(BigInt, BigInt)] = {
    val xy0 = pell(D)
    OrderedMergedIterator(fxys map { fxy =>
      (Iterator single fxy) ++ (pellIterator(D, xy0) map { pellAdd(D, fxy, _) })
    })
  }

  // c * c < D
  // http://www.jpr2718.org/pell.pdf
  def generalPellSimple(D: Long, N: BigInt) = {
    val xys = cfEval(sqrtCf(D) map { _._1 }) takeTo { case (x, y) => x * x - D * y * y != 1 }
    val fxys = for {
      (x, y) <- xys
      n = x * x - D * y * y
      (q, r) = divide(N.toBigInt, n)
      if q > 0
      q2 = isqrt(q)
      if r == 0 && q2 * q2 == q
    } yield (x * q2, y * q2)
    fxys.toList.sorted
  }

  // http://www.jpr2718.org/pell.pdf
  def generalPellBruteForce(D: Long, N: BigInt) = {
    val (x0, y0) = pell(D)

    val L1 = {
      val x = if (N > 0)
        BigDecimal(0)
      else
        BigDecimalMath.sqrt(-N.toBigDecimal / D.toBigDecimal)
      x.setScale(0, BigDecimal.RoundingMode.FLOOR).toBigInt
    }

    val L2 = {
      val x = if (N > 0)
        BigDecimalMath.sqrt(0.5 * N.toBigDecimal * (x0.toBigDecimal - 1) / D.toBigDecimal)
      else
        BigDecimalMath.sqrt(-0.5 * N.toBigDecimal * (x0.toBigDecimal + 1) / D.toBigDecimal)
      x.setScale(0, BigDecimal.RoundingMode.CEILING).toBigInt
    }

    val fxys = for {
      y <- L1 to L2
      x2 = N + D * y * y
      x = isqrt(x2)
      if x * x == x2
      (x1, y1) <- {
        val signN = if (N > 0) 1 else -1
        val (x1, y1) = pellAdd(D, (x0, y0), (signN * x, -signN * y))
        val equiv = pellEquiv(D, N, (x, y), (-x, y))
        (x, y) :: (if (!equiv) (x1, y1) :: Nil else Nil)
      }
    } yield (x1, y1)
    fxys.sorted.toList
  }

  def generalPell(D: Long, c: BigInt) = {
    if (c == 1)
      pell(D) :: Nil
    else if (c == -1)
      negPell(D) :: Nil
    else if (c * c < D)
      generalPellSimple(D, c)
    else
      generalPellBruteForce(D, c)
  }

  case class OrderedMergedIterator[A: Ordering](ts: Seq[Iterator[A]])
    extends Iterator[A] {
    val Q = mutable.SortedSet.empty[(A, Int)]
    for ((t, i) <- ts.zipWithIndex)
      Q += ((t.next, i))

    def next(): A = {
      val (x, i) = Q.head
      Q -= ((x, i))
      val t = ts(i)
      if (t.hasNext)
        Q += ((t.next, i))
      x
    }

    def hasNext = !Q.isEmpty
  }

  object Vec2 {
    def exp(th: Double) = Vec2(cos(th), sin(th))
  }

  case class Vec2(x: Double, y: Double) {
    def unary_-() = Vec2(-x, -y)
    def +(q: Vec2) = Vec2(x + q.x, y + q.y)
    def -(q: Vec2) = this + -q
    def inv = {
      val d = x * x - y * y
      Vec2(x / d, -y / d)
    }
    def *(q: Vec2) = Vec2(x * q.x - y * q.y, x * q.y + y * q.x)
    def /(q: Vec2) = this * q.inv

    def *(d: Double) = Vec2(d * x, d * y)
    def /(d: Double) = Vec2(x / d, y / d)
    def *:(d: Double) = this * d

    def dot(q: Vec2) = x * q.x + y * q.y
    def det(q: Vec2) = x * q.y - y * q.x

    def norm = Math.sqrt(norm2)
    def norm2 = x * x + y * y
    def unit = this / norm
    def slope = y / x

    def proj(q: Vec2) = ((this dot q) / q.norm) *: q.unit
    def rej(q: Vec2) = this - (this proj q)

    override def toString = "(" + x.toString + "," + y.toString + ")"
  }

  case class Vec2i[T: Integral](x: T, y: T) {
    val integral = implicitly[Integral[T]]
    import integral._
    def unary_-() = Vec2i(-x, -y)
    def +(q: Vec2i[T]) = Vec2i(x + q.x, y + q.y)
    def -(q: Vec2i[T]) = this + -q
    def inv = {
      val d = x * x - y * y
      Vec2i(x /~ d, -y /~ d)
    }
    def *(q: Vec2i[T]) = Vec2i(x * q.x - y * q.y, x * q.y + y * q.x)
    def /(q: Vec2i[T]) = this * q.inv

    def *(d: T) = Vec2i(d * x, d * y)
    def /(d: T) = Vec2i(x /~ d, y /~ d)
    def *:(d: T) = this * d

    def dot(q: Vec2i[T]) = x * q.x + y * q.y
    def det(q: Vec2i[T]) = x * q.y - y * q.x
    def ccw(q: Vec2i[T]) = (this det q) > zero

    def norm2 = x * x + y * y

    override def toString = "(" + x.toString + "," + y.toString + ")"
  }

  def quadratic(a: Double, b: Double, c: Double) =
    for (k <- 1 :: -1 :: Nil) yield (-b + k * Math.sqrt(b * b - 4 * a * c)) / (2 * a)

  def iterateTo[A, B](a: A)(f: A => Either[A, B]): B = {
    def g(a: A): B = {
      f(a) match {
        case Left(a) => g(a)
        case Right(b) => b
      }
    }
    g(a)
  }

  // http://en.wikipedia.org/wiki/Miller%E2%80%93Rabin_primality_test
  def millerRabin[T: Integral](n: T) = {
    val integral = implicitly[Integral[T]]
    import integral._

    def removeTwos(n: T): (T, Int) = {
      val (q, r) = divide(n, one + one)
      if (q > zero && r == zero) {
        val (d, s) = removeTwos(q)
        (d, s + 1)
      } else
        (n, 0)
    }
    val (d, s) = removeTwos(n - one)

    def check(a: T) = {
      val x = powmod(a, d, n)
      if (x == one || x == n - one)
        true
      else
        iterateTo((x, s)) {
          case (x, s) =>
            if (s == 0) Right(false)
            else {
              val y = x * x % n
              if (y == 1) Right(false)
              else if (y == n - one) Right(true)
              else Left(y, s - 1)
            }
        }
    }

    // Just like Maple
    val as = List(2, 3, 5, 7, 11) map fromInt takeWhile (_ < n - one)
    as forall check
  }

  def maxSubarray[T: Integral](xs: TraversableOnce[T]) = {
    val integral = implicitly[Integral[T]]
    import integral._

    val (a, b) = ((zero, zero) /: xs) {
      case ((a, b), x) =>
        val a2 = max(a + x, x)
        (a2, max(a2, b))
    }
    b
  }

  def lcg(m: Long, a: Long, c: Long, x0: Long) =
    (Iterator iterate x0) { x => (a * x + c) % m } drop 1

  //def signum(x: BigInt) = BigInt(if (x > 0) 1 else if (x < 0) -1 else 0)

  def subsets[T](xs: List[T]): Iterator[List[T]] =
    xs match {
      case hd :: tl =>
        for {
          k <- List(false, true).iterator
          ys <- subsets(tl)
        } yield if (k) hd :: ys else ys
      case Nil => Iterator single Nil
    }

  object Rational {
    def apply(a: BigInt, b: BigInt) = {
      val g = gcd(a, b)
      val k = signum(b)
      new Rational(k * a / g, k * b / g)
    }

    def exact(a: BigInt, b: BigInt) = new Rational(a, b)
  }

  class Rational(_a: BigInt, _b: BigInt) {
    def a = _a
    def b = _b

    def +(y: Rational) =
      Rational(a * y.b + b * y.a, b * y.b)
    def unary_- = Rational.exact(-a, b)
    def -(y: Rational) = this + -y

    def *(y: Rational) =
      Rational(a * y.a, b * y.b)
    def unary_~ = Rational.exact(signum(a) * b, signum(a) * a)
    def /(y: Rational) = this * ~y
    def *:(x: Int) = Rational(x * a, b)

    def <(y: Rational) = a * y.b - b * y.a < 0
    def <=(y: Rational) = a * y.b - b * y.a <= 0
    override def equals(o: Any) = {
      val y = o.asInstanceOf[Rational]
      y != null && a == y.a && b == y.b
    }

    def abs = Rational.exact(signum(a) * a, b)

    override def hashCode() = a.hashCode ^ b.hashCode

    def toDouble = a.toDouble / b.toDouble
    override def toString = a.toString + "/" + b.toString
  }

  // a + b * sqrt(d)
  case class Quadratic(a: Rational, b: Rational, d: Int) {
    def +(y: Quadratic) = {
      require(d == y.d)
      Quadratic(a + y.a, b + y.b, d)
    }
    def unary_- = Quadratic(-a, -b, d)
    def -(y: Quadratic) = this + -y

    def *(y: Quadratic) =
      Quadratic(a * y.a + Rational(d, 1) * b * y.b, a * y.b + b * y.a, d)
    def unary_~ = Quadratic(a / norm, -b / norm, d)
    def /(y: Quadratic) = this * ~y
    def *:(x: Int) = Quadratic(x *: a, x *: b, d)

    def <(y: Quadratic) = toDouble < y.toDouble
    def norm = a * a - Rational(d, 1) * b * b
    override def equals(o: Any) = {
      val y = o.asInstanceOf[Quadratic]
      y != null && a == y.a && b == y.b && d == y.d
    }

    override def hashCode() = a.hashCode ^ b.hashCode ^ d.hashCode

    def toDouble = a.toDouble + b.toDouble * Math.sqrt(d)
    override def toString = a.toString + "+" + b.toString + "*sqrt(" + d + ")"
  }

  /* 
   * True if p is on segment a-b.
   *  - Assume a != b
   *  - True at endpoints      
   */
  def xPtSeg[T: Integral](p: Vec2i[T], a: Vec2i[T], b: Vec2i[T]) = {
    val integral = implicitly[Integral[T]]
    import integral._
    abs((p - a) det (b - a)) <= zero &&
      ((p - a) dot (b - a)) >= zero &&
      ((p - b) dot (a - b)) >= zero;
  }

  /* 
   * True if segment a-b intersects segment c-d 
   *  -- True at endpoints. 
   */
  def xSegSeg[T: Integral](a: Vec2i[T], b: Vec2i[T], c: Vec2i[T], d: Vec2i[T]) = {
    xSegSegOpen(a, b, c, d) ||
      xPtSeg(a, c, d) ||
      xPtSeg(b, d, c) ||
      xPtSeg(c, a, b) ||
      xPtSeg(d, b, a);
  }

  /* 
   * True if segment a-b intersects segment c-d 
   *  -- False at endpoints. 
   *  -- False if segments are parallel. 
   */
  def xSegSegOpen[T: Integral](a: Vec2i[T], b: Vec2i[T], c: Vec2i[T], d: Vec2i[T]) = {
    val integral = implicitly[Integral[T]]
    import integral._
    val ta = (c - a) det (d - a)
    val tb = (d - b) det (c - b)
    val tc = (a - c) det (b - c)
    val td = (b - d) det (a - d)
    val signum = integral.signum(_)

    signum(ta) != 0 && signum(ta) == signum(tb) &&
      signum(tc) != 0 && signum(tc) == signum(td);
  }

  def inside[T: Integral](ps: Seq[Vec2i[T]], x: Vec2i[T]) =
    0 until ps.length forall { i =>
      (ps((i + 1) % ps.length) - ps(i)) ccw (x - ps(i))
    }

  /*
  def xLineLine[T: Integral](a: Vec2i[T], b: Vec2i[T], c: Vec2i[T], d: Vec2i[T]) = 
    ((a det b) *: (c - d) - (c det d) *: (a - b)) / ((a - b) det (c - d))
  */

  val lfgIterator = new Iterator[Int] {
    var k = 0
    val Q = mutable.Queue.empty[Int]
    def hasNext = true
    def next = {
      k += 1
      if (k <= 55) {
        val c = ((100003 - 200003L * k + 300007L * k * k * k) % 1000000).toInt
        Q enqueue c
        c
      } else {
        val a = Q.dequeue
        val b = Q(55 - 24 - 1)
        val c = (a + b) % 1000000
        Q enqueue c
        c
      }
    }
  }

  def bbs[T: Integral](x0: T, m: T) = {
    val integral = implicitly[Integral[T]]
    import integral._
    (Iterator iterate x0) { x => x * x % m }
  }

  def runLengthEncoding[T](xs: Iterator[T]) =
    new Iterator[(Int, T)] {
      var x: Option[T] = None
      var y: Option[T] = None
      def hasNext = x.isDefined || xs.hasNext
      def next = {
        var c = 1
        if (x.isEmpty)
          x = Some(xs.next)
        while (xs.hasNext && { y = Some(xs.next); y.get == x.get })
          c += 1

        val r = (c, x.get)
        x = y
        y = None
        r
      }
    }

  // ax^2 + bxy + cy^2 == dz^d
  // http://mathworld.wolfram.com/DiophantineEquation2ndPowers.html
  def diophantine2(abcd: (Long, Long, Long, Long), xyz0: (Long, Long, Long))(u: Long, v: Long) = {
    val (a, b, c, d) = abcd
    val (m, n, p) = xyz0
    val x = (a * m + b * n) * u * u + 2 * c * n * u * v - c * m * v * v
    val y = -a * n * u * u + 2 * a * m * u * v + (b * m + c * n) * v * v
    val z = p * (a * u * u + b * u * v + c * v * v)
    (x, y, z)
  }

  def rotate[T](xs: List[T], n: Int): List[T] = {
    val split = xs splitAt n
    split._2 ::: split._1
  }

  // mode is valid [full, same, valid]
  def convolve(xs: Seq[Int], ys: Seq[Int]) = {
    val zs = mutable.Buffer.fill(xs.length + ys.length - 1)(0)
    for {
      (x, xi) <- xs.zipWithIndex
      (y, yi) <- ys.zipWithIndex
    } zs(xi + yi) += x * y
    zs
  }

  def sums[A: Numeric, Repr[A] <: TraversableOnce[A], That](xs: Repr[A])(
    implicit bf: CanBuildFrom[Repr[A], A, That]) = {
    val numeric = implicitly[Numeric[A]]
    import numeric._

    var sum = zero
    val builder = bf()
    builder += sum
    for (x <- xs) {
      sum += x
      builder += sum
    }
    builder.result
  }

  def sums[A: Numeric](xs: Iterator[A]) = {
    val numeric = implicitly[Numeric[A]]
    import numeric._

    var s = zero

    (Iterator single s) ++ new Iterator[A] {
      def hasNext = xs.hasNext
      def next = {
        val x = xs.next
        s += x
        s
      }
    }
  }

  def runningHistogram[A](xs: Iterator[A]) = {
    var M = Map.empty[A, Int] withDefaultValue 0

    (Iterator single M) ++ new Iterator[Map[A, Int]] {
      def hasNext = xs.hasNext
      def next = {
        val x = xs.next
        M = M updated (x, M(x) + 1)
        M
      }
    }
  }

  def runningCount(xs: Iterator[Boolean]) = {
    var c = 0L
    (Iterator single c) ++ new Iterator[Long] {
      def hasNext = xs.hasNext
      def next = {
        val x = xs.next
        if (x) c += 1L
        c
      }
    }
  }

  def pythagoreanTriple[T: Integral](m: T, n: T, k: T) =
    (k * (m * m - n * n),
      2 * k * m * n,
      k * (m * m + n * n))

}

// https://gist.github.com/oxlade39/5752033
object BigDecimalMath {
  def sqrt(x: BigDecimal): BigDecimal = {
    val maxIterations = x.mc.getPrecision + 1

    val guessSteam: Stream[BigDecimal] = newtonRaphsonApproximations(x).take(maxIterations)
    val exactMatch: Option[Stream[BigDecimal]] = guessSteam.sliding(2).find(a => a(0) == a(1))
    val root: Stream[BigDecimal] = exactMatch.getOrElse(Stream(guessSteam.last))

    root(0)
  }

  /**
   * A sequence of BigDecimals the tend towards the square root of toSqrt.
   * Using the Newton Raphson Approximations http://en.wikipedia.org/wiki/Newton's_method
   * @param toSqrt the value to find the root of
   * @param guess the first guess to iterate over (typically toSqrt/2)
   * @return
   */
  private[this] def newtonRaphsonApproximations(toSqrt: BigDecimal, guess: BigDecimal): Stream[BigDecimal] =
    Stream.cons(guess, newtonRaphsonApproximations(toSqrt, ((toSqrt / guess) + guess) / 2))

  private[this] def newtonRaphsonApproximations(toSqrt: BigDecimal): Stream[BigDecimal] =
    newtonRaphsonApproximations(toSqrt, toSqrt / 2)

}
