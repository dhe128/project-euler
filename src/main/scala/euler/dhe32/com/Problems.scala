package euler.dhe32.com

import scala.collection._
import scala.collection.generic.CanBuildFrom
import Utils._
import Implicits._
import scala.util.Random
import scala.io.Source
import scalaz._
import spire.algebra._
import spire.math._
import spire.implicits._
import spire.syntax.literals._
import spire.syntax.literals.si._
import scala.concurrent._
import ExecutionContext.Implicits.global

object Problems {
  def p1(N: Int = 1000) = {
    val xs = 1 until N filter (x => x % 3 == 0 || x % 5 == 0)
    xs.sum
  }

  def p2(N: Int = 4000000) = {
    val xs = Iterator from 0 map fibonacci filter (_ % 2 == 0) takeWhile (_ < N)
    xs.sum
  }

  def p3(N: BigInt = BigInt("600851475143")) =
    factor(N).last

  def p4(N: Int = 3) = {
    def isPalindrome(x: String): Boolean = {
      val z = x.length() / 2
      val a = x.substring(0, z)
      val b = x.reverse.substring(0, z)
      a == b
    }

    def ndigit(n: Int): Seq[BigInt] = BigInt(10).pow(n - 1) to (BigInt(10).pow(n) - 1)

    val xs =
      for {
        i <- ndigit(N)
        j <- ndigit(N)
        if isPalindrome((i * j).toString())
      } yield i * j

    xs.max
  }

  def p5(N: Int = 20) =
    (1 /: (1 to N))(Utils.lcm)

  def p6(N: Int = 100) = {
    val a = (1 to N map { _ ** 2 }).sum
    val b = (1 to N).sum
    b * b - a
  }

  def p7(N: Int = 10001) = {
    val piinvN = inverseMonotonic(x => x / Math.log(x))(N)
    val M = (1.2 * piinvN).toInt
    val ps = primes(M)
    (ps drop (N - 1)).next
  }

  def p8(rawData: String = StringData.s008) = {
    val t = rawData filter { _.isDigit } map { _.asDigit }
    val r = (0 to t.length - 5) map { i => t.slice(i, i + 5) } map { z => (1 /: z)(_ * _) }
    r.max
  }

  def p9(N: Int = 1000) = {
    val xs = for {
      a <- 1 to N
      b <- 1 to N - a
    } yield (a, b, N - a - b)
    val ys = xs filter { z => val (a, b, c) = z; a * a + b * b == c * c }
    val y = ys(0)
    y._1 * y._2 * y._3
  }

  def p10(N: Int = 2000000) =
    (primes(N) map { _.toLong }).sum

  def p11(rawData: String = StringData.s011, N: Int = 20) = {
    def data = (rawData split "\\s+" map (_.toInt)).toIndexedSeq
    def D = (data sliding (N, N)).toIndexedSeq

    def Hline(i: Int) =
      for (j <- 0 until N)
        yield D(j)(i)

    def Vline(i: Int) = D(i)
    def Aline(i: Int) = {
      if (i > 0)
        for (j <- 0 until (N - i))
          yield D(i + j)(j)
      else
        for (j <- 0 until (N + i))
          yield D(j)(j - i)
    }

    def Bline(i: Int) = {
      if (i > 0)
        for (j <- 0 until (N - i))
          yield D(N - j - 1)(i + j)
      else
        for (j <- 0 until (N + i))
          yield D(N + i - j - 1)(j)
    }

    val lines = (
      (0 until N map Hline)
      ++ (0 until N map Vline)
      ++ ((-N + 1) until N map Aline)
      ++ ((-N + 1) until N map Bline))

    def doLine(xs: Seq[Int]) = (xs sliding 4 map (_.product)).max

    (lines map doLine).max
  }

  def p12(N: Int = 500) = {
    val iopt = Iterator from 0 map { n => n * (n + 1) / 2 } find { numDivisors(_) > N }
    iopt.get
  }

  def p13(rawData: String = StringData.s013) = {
    val data = rawData split "\\s+" map { BigInt(_) }
    data.sum.toString take 10
  }

  def p14(N: Int = 1000000) = {
    val collatzHeight = memoizeY(
      (n: BigInt, f: BigInt => Int) =>
        if (n == 1) 1 else f(collatz(n)) + 1)

    BigInt(1) until BigInt(N) maxBy collatzHeight
  }

  def p15(N: Int = 20) =
    ncr(2 * N, N)

  def p16(N: Int = 1000) = {
    val x = BigInt(2) pow N
    val xs = x.toString.toSeq map { _.toInt - '0'.toInt }
    xs.sum
  }

  def p17(N: Int = 1000) = {
    def numsList = List("", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten", "eleven", "twelve", "thirteen", "fourteen", "fifteen", "sixteen", "seventeen", "eighteen", "nineteen")
    val numsMap = mutable.Map() ++ (numsList.zipWithIndex map (_.swap))
    numsMap += (20 -> "twenty")
    numsMap += (30 -> "thirty")
    numsMap += (40 -> "fourty")
    numsMap += (50 -> "fifty")
    numsMap += (60 -> "sixty")
    numsMap += (70 -> "seventy")
    numsMap += (80 -> "eighty")
    numsMap += (90 -> "ninty")

    def repr(n: Int): List[String] = {
      if (numsMap contains n)
        numsMap(n) :: Nil
      else if (n == 1000)
        "one" :: "thousand" :: Nil
      else if (n >= 100) {
        val (q, r) = divide(n, 100)
        numsMap(q) :: "hundred" :: {
          if (r == 0) Nil
          else "and" :: repr(r)
        }
      } else if (n >= 10) {
        val r = n % 10
        numsMap(n - r) :: {
          if (r == 0) Nil
          else repr(r)
        }
      } else
        Nil
    }

    val s = 1 to N map { n => (repr(n) map { _.length }).sum }
    s.sum
  }

  def p18(rawData: String = StringData.s018) = {
    def f(bs: List[Int], as: List[Int]) = {
      val cs = (as sliding 2).toList zip bs
      cs collect { case (a0 :: a1 :: Nil, b) => max(a0, a1) + b }
    }

    val nss = rawData split "\n" map { line => (line split "\\s" map { _.toInt }).toList }
    (nss :\ Nil.padTo(nss.length + 1, 0))(f).head
  }

  def p19() = {
    def isSunday(d: Int) = (d % 7) == 6

    val dm = List(31, 0, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31)
    def daysInMonth(m: Int, y: Int) = {
      if (m == 1)
        if (y % 4 == 0 && y % 400 != 100)
          29
        else
          28
      else
        dm(m)
    }

    def sundaysUntil(Y: Int): Int = {
      var d = 0
      var r = 0
      for {
        y <- 0 to Y
        m <- 0 until 12
      } yield {
        d += daysInMonth(m, y)
        if (isSunday(d))
          r += 1
      }
      r
    }

    sundaysUntil(101) - sundaysUntil(1)
  }

  def p20(n: Int = 100) = {
    val nf = factorial(n)
    (nf.toString.toSeq map { _.toInt - '0'.toInt }).sum
  }

  def p21(N: Int = 10000) = {
    val xs = (2 until N) filter { a =>
      val b = sigmaProper(a, 1)
      b != a && sigmaProper(b, 1) == a
    }
    xs.sum
  }

  def p22(rawData: String = StringData.s022) = {
    def alphaVal(s: String) = (s map { _ - 'A' + 1 }).sum

    val data = rawData split "," map { _ drop 1 dropRight 1 }
    val names = data.sorted
    val scores = names.zipWithIndex map { case (s, i) => alphaVal(s) * (i + 1) }
    scores.sum
  }

  def p23(N: Int = 28123) = {
    val asList = (2 to N) filter { a => sigmaProper(a, 1) > a }
    val as = asList.toSet

    val xs = (1 to N) filterNot { n =>
      (1 until n) exists { x => (as contains x) && (as contains (n - x)) }
    }
    xs.sum
  }

  def p24(N: Int = 1000000) =
    lexico(N - 1, 10) map { _.toString } mkString ""

  def p25(N: Int = 1000) =
    (Iterator from 0 find { fibonacci(_).toString.length == N }).get

  def p26(N: Int = 1000) = {
    def longDivide(n: Int, d: Int): Int = {
      val (q, r) = divide(10 * n, d)
      if (r == 0)
        0
      else if (r == 1)
        1
      else
        longDivide(r, d) + 1
    }

    def cycleLength(x: Int): Int = {
      val x2 = (factor(x) filterNot { x => x == 2 || x == 5 }).product
      longDivide(1, x2)
    }

    (1 to N) maxBy cycleLength
  }

  def p27(N: Int = 1000) = {
    def quadratic(a: Int, b: Int): Int => Int =
      x => x * x + a * x + b

    val qs = for {
      a <- (-(N - 1)) until (N - 1)
      b <- (-(N - 1)) until (N - 1)
    } yield (a, b)

    val (a, b) = qs maxBy {
      case (a, b) =>
        val f = quadratic(a, b)
        val ps = Iterator from 0 takeWhile { z => isPrime(f(z)) }
        ps.length
    }
    a * b
  }

  def p28(N: Int = 1001) =
    1 + ((1 to (N - 1) / 2) map (_ * 2) map (x => 4 * x * x + 2 * x + 4)).sum

  def p29(N: Int = 100) = {
    val xs = for {
      a <- 2 to N
      b <- 2 to N
    } yield BigInt(a) pow b

    xs.distinct.length
  }

  def p30(N: Int = 5) = {
    def ok(x: Int) = {
      val xs = split10(x)
      (xs count (_ != 0)) > 1 &&
        (xs map (_ ** N)).sum == x
    }

    val ys = (1 to (N * (9 ** N).toInt)) filter ok
    ys.sum
  }

  def p31(N: Int = 200) = {
    val coins = List(1, 2, 5, 10, 20, 50, 100, 200)
    def iter(xs: Stream[Int], coin: Int) = {
      def ys: Stream[Int] = (xs take coin) #::: (xs drop coin zip ys map { case (a, b) => a + b })
      ys
    }

    (coins foldLeft (1 #:: Stream.fill(N)(0)))(iter).last
  }

  def p31b(N: Int = 200) = {
    val coins = List(1, 2, 5, 10, 20, 50, 100, 200)

    val f = memoizeY(
      (z: (Int, Int), f: ((Int, Int)) => Int) => {
        val (n, j) = z
        if (n == 0)
          1
        else if (j == -1)
          0
        else {
          val ys = Iterator from 0 takeWhile (n - _ * coins(j) >= 0) map { k => f(n - k * coins(j), j - 1) }
          ys.sum
        }
      })

    f(N, coins.length - 1)
  }

  def p32(N: Int = 9) = {
    val ts = for {
      ys <- (1 to N).toList.permutations
      zs <- (1 to N - 1).toList combinations 2
    } yield {
      val a = ys slice (0, zs(0))
      val b = ys slice (zs(0), zs(1))
      val c = ys slice (zs(1), ys.length)
      (join10(a), join10(b), join10(c))
    }

    val us = ts filter (x => x._1 * x._2 == x._3)
    (us map (_._3)).toList.distinct.sum
  }

  def p33() = {
    val ts = for {
      a <- 10 to 99
      b <- a + 1 to 99
      as = split10(a)
      bs = split10(b)
      ai <- 0 until 2
      bi <- 0 until 2
      if 1.0 * a / b == 1.0 * as((ai + 1) % 2) / bs((bi + 1) % 2) && as(ai) == bs(bi) && bs(bi) != 0
    } yield (a, b)
    val rx = (ts map (_._1)).product
    val ry = (ts map (_._2)).product
    ry / gcd(rx, ry)
  }

  def p34() = {
    val xs = (10 until factorial(9).toInt) filter (x => (split10(x) map factorial.apply).sum == x)
    xs.sum
  }

  def p35(N: Int = 1000000) = {
    val ps = primes(N).to[SortedSet]
    ps count {
      x =>
        val ys = split10(x)
        (0 until ys.length) forall { z => ps contains join10(rotate(ys, z)) }
    }
  }

  def p36(N: Int = 1000000) = {
    def isPalindrome[T](xs: Seq[T]) =
      (xs take xs.length / 2) == (xs.reverse take xs.length / 2)

    val xs = 1 until N filter (x => isPalindrome(split10(x)) && isPalindrome(splitBase(2, x)))
    xs.sum
  }

  def p37(N: Int = 1000000) = {
    val ps = primes(N).toSet
    def isPrime(x: Int) = ps contains x

    val lefts = mutable.Map[Int, Boolean]()
    def isLeft(x: Int): Boolean = {
      if (!(lefts contains x)) {
        val y = join10(split10(x) drop 1)
        lefts(x) = if (y == 0) isPrime(x) else isPrime(x) && isLeft(y)
      }
      lefts(x)
    }

    val rights = mutable.Map[Int, Boolean]()
    def isRight(x: Int): Boolean = {
      if (!(rights contains x)) {
        val y = join10(split10(x) dropRight 1)
        rights(x) = if (y == 0) isPrime(x) else isPrime(x) && isRight(y)
      }
      rights(x)
    }

    val xs = 1 until N filter (x => isLeft(x) && isRight(x)) filter (_ > 10)
    xs.sum
  }

  def p38(N: Int = 1000000) = {
    val ts = for {
      x <- 1 to N
      y <- 2 to 4
      zs = 1 to y map (_ * x) flatMap split10
      if zs.sorted == (1 to 9)
    } yield join10(zs)
    ts.max
  }

  def p39(N: Int = 1000) = {
    def count(n: Int) = {
      val zs = for {
        a <- 1 to n
        b <- a to n
        c = n - a - b
      } yield (a, b, c)
      zs count { case (a, b, c) => a * a + b * b == c * c }
    }

    1 to N maxBy count
  }

  def p40(N: Int = 1000000) = {
    def index(n: Int): Int = {
      val e = ilog10(n)
      (e + 1) * (n - (10 ** e)) + i2(e)
    }

    def i2(e: Int): Int = if (e == 0) 1 else e * 9 * (10 ** (e - 1)) + i2(e - 1)

    def champer(n: Int) = {
      val z = greatestLowerBound(index, 0, N)(n)
      split10(z)(n - index(z))
    }

    val ts = (1 to ilog10(N)) map (10 ** _) map champer
    ts.product
  }

  def p41(N: Int = 999999999) = {
    val ps = primes(N)

    val ts = ps filter { x =>
      val ys = split10(x)
      ys.sorted == (1 to ys.length)
    }
    ts.max
  }

  def p42(source: Source = getResource("words.txt")) = {
    val wordr = "\"(\\w+)\"".r
    val words = wordr findAllIn source.mkString map { case wordr(word) => word }

    val ts = 1 to 100 map (x => x * (x + 1) / 2)
    def isTriangle(x: Int) = binarySearch(ts, x)

    val zs = words map (word => (word map (_ - 'A' + 1)).sum) filter isTriangle
    zs.length
  }

  def p43() = {
    def joinBase(base: Int, xs: Seq[Int]) =
      (xs.reverse.zipWithIndex map (z => z._1 * (BigInt(base) pow z._2))).sum

    def join10 = (xs: Seq[Int]) => joinBase(10, xs)

    val ps = primes(18).toIndexedSeq
    val ts = (0 to 9).permutations filter { ys =>
      (0 until ps.length) forall { i => join10(ys.slice(i + 1, i + 4)) % ps(i) == 0 }
    }
    (ts map join10).sum
  }

  def p44(N: Int = 10000) = {
    val ps = 0 until N map { x => x * (3 * x - 1) / 2 }

    val ts = for {
      i <- 1 until N
      j <- i + 1 until N
      a = ps(j) + ps(i)
      b = ps(j) - ps(i)
      if binarySearch(ps, a) && binarySearch(ps, b)
    } yield b
    ts.min
  }

  def p45(N: Int = 200000) = {
    val ts = 1 until N map BigInt.apply map { x => x * (x - 1) / 2 }
    val ps = 1 until N map BigInt.apply map { x => x * (3 * x - 1) / 2 }
    val hs = 1 until N map BigInt.apply map { x => x * (2 * x - 1) }

    val xs = ts intersect ps intersect hs
    xs.sorted.toList(2)
  }

  def p46(N: Int = 10000) = {
    val ps = primes(N).toSet

    def ok(t: Int) =
      (1 to isqrt(t) exists { x => ps contains (t - 2 * x * x) })

    val ts = 2 to N filter (x => x % 2 == 1 && !(ps contains x)) filterNot ok
    ts.min
  }

  def p47(N: Int = 4) = {
    val xs = Iterator from 1 map (factor(_))
    val ts = xs sliding N filter { _ forall { _.distinct.length == N } }
    ts.next.head.product
  }

  def p48(N: Int = 1000) = {
    val M = BigInt(10000000000L)
    val xs = 1 to N map { x => Utils.powmod(BigInt(x), BigInt(x), M) }
    xs.sum % M
  }

  def p49() = {
    val ps = (primesRange(1000, 10000) map (_.toInt)).toIndexedSeq

    val ts = for {
      i <- 0 until ps.length
      j <- i + 1 until ps.length
      pi = ps(i)
      pj = ps(j)
      pk = 2 * pj - pi
      if binarySearch(ps, pk) && split10(pi).sorted == split10(pj).sorted && split10(pi).sorted == split10(pk).sorted
    } yield List(pi, pj, pk)
    (ts.tail.head flatMap split10).mkString
  }

  def p50(N: Int = 1000000) = {
    val ps = primes(N).toIndexedSeq

    val ts = for {
      i <- (1 until ps.length).par
      qs = (ps view (i, ps.length)).iterator
      (sum, len) <- (sums(qs) takeWhile (_ <= N)).zipWithIndex
      if binarySearch(ps, sum)
    } yield (len, sum)

    (ts maxBy (_._1))._2
  }

  def p51(N: Int = 8) = {
    val M = 1000000
    val ps = primes(M).toIndexedSeq

    val ct = mutable.Map[List[Int], Int]() withDefaultValue 0
    for {
      p <- ps
      pz = split10(p)
      xz <- ndIndex(List.fill(pz.length)(2))
      if (pz zip xz filter (_._2 == 1)).distinct.length == 1
    } yield {
      val qz = pz zip xz map { z => if (z._2 == 1) -1 else z._1 }
      ct(qz) += 1
    }

    val ts = for {
      qz <- ct filter (_._2 >= N) map (_._1)
      y <- 0 until 9 filter (x => !(qz contains x))
      pz = qz map (z => if (z == -1) y else z)
      if pz.head != 0
      p = join10(pz)
      if binarySearch(ps, p)
    } yield p

    ts.min
  }

  def p52 =
    // well known result
    142857

  def p53(N: Int = 1000000) = {
    def logncr(n: Int, r: Int): Double =
      ((r + 1) to n map (_.toDouble) map log10).sum - (1 to (n - r) map (_.toDouble) map log10).sum

    val ts = for {
      x <- 1 to 100
      y <- 1 to 100
      if logncr(x, y) >= log10(N)
    } yield 1
    ts.length
  }

  def p54(source: Source = getResource("poker.txt")) =
    Problem054(source)

  object Problem054 {
    case class Card(rank: Int, suit: Char)

    object Card {
      def fromString(s: String) =
        Card(s(0) match {
          case 'T' => 10
          case 'J' => 11
          case 'Q' => 12
          case 'K' => 13
          case 'A' => 14
          case x: Char => x - '0'
        }, s(1))
    }

    def hand(_cards: List[Card]): List[Int] = {
      val cards = _cards sortBy (-_.rank)
      val isFlush = (cards map (_.suit)).distinct.length == 1
      val isStraight = (cards.head.rank to cards.last.rank by -1) == (cards map (_.rank))
      val group = (cards groupBy (_.rank)).toList map { case (rank, seq) => (rank, seq.length) } sortBy (z => (-z._2, -z._1))

      if (isFlush && isStraight)
        8 :: cards.head.rank :: Nil
      else if (group.head._2 == 4)
        7 :: (group map (_._1))
      else if ((group map (_._2)) == List(3, 2))
        6 :: (group map (_._1))
      else if (isFlush)
        5 :: (cards map (_.rank))
      else if (isStraight)
        4 :: cards.head.rank :: Nil
      else if (group.head._2 == 3)
        3 :: (group map (_._1))
      else if ((group map (_._2)) == List(2, 2, 1))
        2 :: (group map (_._1))
      else if (group.head._2 == 2)
        1 :: (group map (_._1))
      else
        0 :: (cards map (_.rank))
    }

    def apply(source: Source) = {
      val cardr = """\w+""".r
      val ts = for {
        line <- source.getLines
        cards = cardr findAllIn line map Card.fromString
      } yield cards.toList splitAt 5

      ts count { case (c1, c2) => (hand(c1) compare hand(c2)) > 0 }
    }
  }

  def p55(N: Int = 10000) = {
    val M = 50
    def isLychrel(x: Int) = {
      def f(x: BigInt, k: Int): Boolean = {
        val ys = split10(x)
        k == M || (k == 0 || ys != ys.reverse) && f(x + joinBase[BigInt](10, ys.reverse), k + 1)
      }
      f(x, 0)
    }

    1 until N count isLychrel
  }

  def p56(N: Int = 100) = {
    val cs = for {
      a <- 1 to N
      b <- 1 to N
      c = BigInt(a) pow b
    } yield c
    (cs map (split10(_).sum)).max
  }

  def p57(N: Int = 1000) = {
    val xs = cfEval(sqrtCf(2) map { _._1 })
    xs take N count { case (x, y) => ilog10(x) > ilog10(y) }
  }

  def p58(N: Int = 10) = {
    def diags = Iterator from 0 map {
      x =>
        if (x == 0)
          List(1)
        else
          (0 until 4).reverse map { y =>
            (2 * x + 1) ** 2 - y * 2 * x
          }
    }

    val counts = (diags scanLeft (0, 0)) {
      case ((n, d), xs) =>
        (n + (xs count isPrime), d + xs.length)
    }

    val ts = counts.zipWithIndex takeWhile {
      case ((n, d), ix) =>
        ix <= 3 || n * N >= d
    }
    2 * (ts.length - 1) + 1
  }

  def p59(source: Source = getResource("cipher1.txt")) = {
    val e = source.getLines.next split "," map (_.toByte)

    def decrypt(e: Seq[Byte], key: Seq[Byte]): IndexedSeq[Byte] =
      (e.sliding(key.length, key.length) flatMap {
        es => es zip key map { case (x, k) => (x ^ k).toByte }
      }).toIndexedSeq

    val scores = ndIndex(26 :: 26 :: 26 :: Nil) parMap {
      z =>
        val key = z map (x => ('a' + x).toByte)
        val d = (decrypt(e, key) map (_.toChar)).mkString
        val score = 1.0 * (d count ("etoain" contains _)) / d.length
        (key, score)
    }

    val key = (scores maxBy (_._2))._1
    (decrypt(e, key) map (_.toInt)).sum
  }

  def p60() = {
    //val N = 5
    val M = 100000000
    val ps = (primes(M) filter (p =>
      p < 10 ||
        (p.toString dropRight 1 exists ("1379" contains _)))).to[SortedSet]

    def isClique(zs: Seq[Int]) = {
      val ys = for {
        u <- zs.iterator
        v <- zs
        if u != v
      } yield (u.toString + v.toString).toInt
      ys forall (ps contains _)
    }

    val ps2 = (ps.iterator takeWhile (_ < 10000)).toList
    val q2s = (ps2 combinations 2 parFilter isClique).toSeq

    def qPlus(qs: Seq[List[Int]]) = {
      val ps = qs.flatten.to[SortedSet]
      (for {
        q <- qs.par
        p <- ps
        if !(q contains p) && isClique(p :: q)
      } yield p :: q).seq
    }

    val q3s = qPlus(q2s)
    val q4s = qPlus(q3s)
    val q5s = qPlus(q4s)

    (q5s map (_.sum)).min
  }

  def p61(N: Int = 8) = {
    def ds = (3 to N map { p =>
      val ns = Iterator from 0 map ngon(p) dropWhile (_ <= 1000) takeWhile (_ < 10000)
      (p, ns.toIndexedSeq groupBy (_ / 100) withDefaultValue Nil)
    }).toMap

    def pPlus(qs: immutable.Set[List[Int]], p: Int) =
      qs flatMap (q => ds(p)(q.head % 100) filterNot { q contains _ } map { _ :: q })

    val pss = (4 to N).permutations map (ps => 3 :: ps.toList)
    val rs = (pss flatMap { ps =>
      val qs = (ds(ps.head) flatMap (_._2) map (_ :: Nil)).toSet
      (qs /: ps.tail)(pPlus) filter (q => q.head % 100 == q.last / 100)
    }).toList

    rs.head.sum
  }

  def p62(N: Int = 5) = {
    def solve(M: Long) = {
      val D = mutable.Map[List[Int], List[Long]]() withDefaultValue Nil
      for {
        c <- Iterator from 1 map (_.toLong ** 3) takeWhile (_ < M)
      } D(split10(c).sorted) ::= c

      val ts = (D.values filter (_.length >= N)).flatten
      if (!ts.isEmpty) Some(ts.min) else None
    }

    tunel(10 ** 9, 10)(solve)
  }

  def p63() = {
    val ys = (0 to 9 map (b => log(10) / log(10.0 / b)) map (floor(_).toInt)).toIndexedSeq
    val zs = 1 to 9 flatMap (b => 0 to ys(b) map (b ** _))
    zs.toSet.size
  }

  def p64(N: Int = 10000) = {
    def sqrtCfCycle(x: Int) = {
      val ks = sqrtCf(x) drop 1
      val seen = mutable.Set[(Long, Long, Long)]()
      ks takeWhile {
        case (k, y) =>
          val b = !(seen contains y)
          seen add y
          b
      }
    }

    def isSquare(x: Int) = isqrt(x) ** 2 == x
    val cycles = 1 to N filterNot isSquare map sqrtCfCycle
    cycles count (_.length % 2 == 1)
  }

  def p65(N: Int = 100) = {
    val zs = Iterator from 0 map { i =>
      if (i == 0)
        2
      else if (i % 3 == 2)
        2 * ((i / 3) + 1)
      else
        1
    }

    val t = (cfEval(zs) drop N - 1).next
    split10(t._1).sum
  }

  def p66(N: Int = 1000) = {
    def isSquare(x: Int) = isqrt(x) ** 2 == x

    val xs = 1 to N filterNot isSquare
    xs maxBy (D => pell(D)._1)
  }

  def p67(source: Source = getResource("triangle.txt")) = {
    def f(bb: List[Int], aa: List[Int]) = {
      val cc = (aa sliding 2).toList zipAll (bb, List(0, 0), 0)
      cc collect { case (a0 :: a1 :: Nil, b) => max(a0, a1) + b }
    }

    val nss = source.getLines map {
      line => (line split "\\s" map { _.toInt }).toList
    }
    (nss :\ List.empty[Int])(f).head
  }

  def p68(N: Int = 5) = {
    val M = 16
    def shift[T](xs: IndexedSeq[T], n: Int = 1) = {
      val (a, b) = xs splitAt n
      b ++ a
    }

    val ns = (1 to 2 * N).reverse.toIndexedSeq
    val ts = for {
      as <- ns combinations N filter (_.sum % N == 0)
      xs <- (ns filterNot (as contains _)).permutations
      segs = as zip xs zip shift(xs)
      sums = segs map { case ((a, x0), x1) => a + x0 + x1 }
      if sums forall (_ == sums.head)
    } yield (shift(segs, N - 1) map { case ((a, x0), x1) => a.toString + x0.toString + x1.toString }).mkString

    ts filter (_.length == M) maxBy (BigInt(_))
  }

  def p69(N: Int = 1000000) =
    1 to N maxBy (n => 1.0 * n / phi(n))

  def p70(N: Int = 10000000) = {
    val ts = 2 until N filter { n =>
      val p = phi(n)
      split10(n).sorted == split10(phi(n)).sorted
    }

    ts minBy (n => 1.0 * n / phi(n))
  }

  def p71(N: Int = 1000000) = {
    val d = (N - 5) / 7 * 7 + 5
    val n = (3 * d - 1) / 7
    n / gcd(n, d)
  }

  def p72(N: Int = 1000000) =
    ((1 to N).par map (x => phi(x).toBigInt)).sum - 1

  def p73(N: Int = 12000) = {
    val ts = for { n <- (1 to N).iterator; d <- 1 to n } yield (d, n)
    ts count { case (n, d) => 2 * n < d && d < 3 * n && gcd(n, d) == 1 }
  }

  def p74(N: Int = 1000000) = {
    val f = memoize((n: BigInt) => (split10(n) map factorial).sum)

    def chain(n: BigInt) = {
      def rec(xs: List[BigInt]): List[BigInt] = {
        val y = f(xs.head)
        if (xs contains y)
          xs
        else
          rec(y :: xs)
      }
      rec(n :: Nil)
    }

    val lengths = 1 to N map (n => (n, chain(n).length))
    val max = lengths maxBy (_._2)
    lengths count (_._2 == max._2)
  }

  def p75(N: Int = 1500000) = {
    def triples(x2: Int) = {
      val x = x2 / 2
      val gs = factor2(x)
      val xgs = gs map (_._2)
      def evalGs(xgs: List[Int]) =
        (xgs zip gs map { case (mc, (p, _)) => p ** mc }).product

      val mns = for {
        mgs <- ndIndex(xgs map (_ + 1))
        m = evalGs(mgs)
        n2gs <- ndIndex((xgs zip mgs) map { case (xc, mc) => xc - mc + 1 })
        n = evalGs(n2gs) - m
        if m > n && n > 0
        k = x / m / (m + n)
      } yield (m, n, k)

      mns map { case (m, n, k) => pythagoreanTriple(m, n, k) }
    }

    (1 to N).par filter (_ % 2 == 0) count { n =>
      val ts = triples(n) map { case (a, b, c) => List(a, b, c).sorted }
      ts.toSet.size == 1
    }
  }

  def p76(N: Int = 100) = pfn(N)

  def p77(N: Int = 5000) = {
    val M = 1000
    val ps = primes(M).toIndexedSeq

    val f = memoizeY((nj: (Int, Int), f: Tuple2[Int, Int] => Int) => {
      val (n, j) = nj

      if (j == 0)
        0
      else if (n == 0)
        0
      else {
        val p = ps(j - 1)
        val as = Iterator from 0 map {
          k => n - k * p
        } takeWhile (_ >= 0)

        (as map (f(_, j - 1))).sum + (if (n % p == 0) 1 else 0)
      }
    })

    def count(n: Int) =
      f(n, ps.length) - (if (binarySearch(ps, n)) 1 else 0)

    (Iterator from 0 find (count(_) > N)).get
  }

  def p78(N: Int = 1000000) =
    (Iterator from 0 find (pfn(_) % N == 0)).get

  def p79() =
    // pen and paper
    "73162890"

  def p80(N: Int = 100, M: Int = 100) = {
    import java.math.MathContext

    val mc = new MathContext(M + 10)
    val zero = BigDecimal(0)(mc)

    def leastStrictUpperBound(f: BigDecimal => BigDecimal, t: BigDecimal)(a: BigDecimal, b: BigDecimal) = {
      val eps = (zero + 1) / ((zero + 10) pow (M + 1))

      def rec(a: BigDecimal, b: BigDecimal): BigDecimal = {
        val mid = (a + b) / 2;
        val d = t - f(mid)
        if (d.abs < eps)
          mid
        else if (d < 0)
          rec(a, mid);
        else
          rec(mid, b);
      }
      rec(a, b)
    }

    def sqrt(n: BigDecimal): BigDecimal =
      leastStrictUpperBound(x => x * x, n)(zero, zero + n)

    def isSquare(n: Int) = isqrt(n) ** 2 == n

    def digits(n: BigDecimal) =
      n.toString filter (c => '0' <= c && c <= '9') map (_ - '0') take 100

    (1 to N filterNot isSquare flatMap (n => digits(sqrt(n)))).sum
  }

  def p81(source: Source = getResource("matrix.txt")) = {
    val D = (source.getLines map (line => line split "," map Integer.parseInt)).toIndexedSeq
    val N = D.length
    type Key = (Int, Int)

    val f = memoizeY(
      (ij: Key, f: Key => Int) => {
        val (i, j) = ij
        if (i + j == -1)
          0
        else if (i == -1 || j == -1)
          1000000
        else {
          val nexts = (i - 1, j) :: (i, j - 1) :: Nil
          D(i)(j) + (nexts map f).min
        }
      })

    f((N - 1, N - 1))
  }

  def p82(source: Source = getResource("matrix.txt")) = {
    val D = (source.getLines map (line => line split "," map Integer.parseInt)).toIndexedSeq
    val N = D.length
    type Key = (Int, Int, Int)

    val f = memoizeY(
      (ij: Key, f: Key => Int) => {
        val (i, j, dir) = ij
        if (j == -1)
          0
        else if (i == -1 || i == N)
          1000000
        else {
          val nexts = mutable.Set.empty[Key]
          if (dir != 1)
            nexts += ((i - 1, j, -1))
          if (dir != -1)
            nexts += ((i + 1, j, 1))
          nexts += ((i, j - 1, 0))
          D(i)(j) + (nexts map f).min
        }
      })

    (0 to N - 1 map (f(_, N - 1, 0))).min
  }

  def p83(source: Source = getResource("matrix.txt")) = {
    val data = (source.getLines map (line => line split "," map Integer.parseInt)).toIndexedSeq
    val N = data.length
    type Key = (Int, Int)

    def D(ij: Key) = data(ij._1)(ij._2)
    def G(ij: Key) = {
      val (i, j) = ij
      var nexts = List.empty[Key]
      if (i != 0)
        nexts ::= (i - 1, j)
      if (i != N - 1)
        nexts ::= (i + 1, j)
      if (j != 0)
        nexts ::= (i, j - 1)
      if (j != N - 1)
        nexts ::= (i, j + 1)
      nexts
    }

    def weight(a: Key, b: Key) = D(b)

    val s = (0, 0)
    val t = (N - 1, N - 1)
    val (dist, prev) = dijkstra(G, s, weight)
    dist(t) + D(s)
  }

  def p84(N: Int = 4) = {
    val M = 40
    type Vec = mutable.Buffer[Double]
    type Mat = mutable.Buffer[Vec]
    def multMat(A: Mat, B: Mat): Mat = {
      val C = mutable.Buffer.tabulate(A.length, B(0).length)((_, _) => 0.0)
      for {
        i <- 0 until A.length
        j <- 0 until B.length
        k <- 0 until B(0).length
      } C(i)(k) += A(i)(j) * B(j)(k)
      C
    }

    def getLine(n: Int) = {
      val L = mutable.Buffer.fill(M)(0.0)

      val go = 0
      val jail = 10
      val tojail = 30
      val cc = 2 :: 17 :: 33 :: Nil
      val ch = 7 :: 22 :: 36 :: Nil

      // triple doubles
      val rolljail = 1.0 / (6 * 6 * 6)
      L(jail) += rolljail

      // dice roll
      for {
        i <- 1 to N
        j <- 1 to N
      } L((n + i + j) % M) += (1.0 - rolljail) / (N * N)

      // go to jail
      L(jail) += L(tojail)
      L(tojail) = 0.0

      // community chest
      for (s <- cc) {
        val s16 = L(s) / 16
        L(s) -= 2.0 * s16
        L(go) += s16
        L(jail) += s16
      }

      // chance
      for (s <- ch) {
        val s16 = L(s) / 16
        L(go) += s16
        L(jail) += s16
        L(11) += s16
        L(24) += s16
        L(39) += s16
        L(5) += s16
        val r = ((s + 5) / 10 * 10 + 5) % M
        L(r) += 2 * s16
        val u = s match {
          case 7 => 12
          case 22 => 28
          case 36 => 12
        }
        L(u) += s16
        L(((s - 3) + M) % M) += s16
        L(s) -= 10 * s16
      }

      L
    }

    val A = (mutable.Buffer tabulate M)(getLine)

    val Aexp = ((Iterator iterate A)(A => multMat(A, A)) drop M).next
    val R = Aexp(0).zipWithIndex sortBy (-_._1)
    (R take 3 map (_._2)).mkString
  }

  def p85(N: Int = 2000000) = {
    val M = 100
    def sq(x: Int) = x * (x - 1) / 2
    def sqInv(x: Double) = Math.ceil((1 + sqrt(1 + 8 * x)) / 2).toInt

    val rects = 1 to M flatMap { m =>
      val n = sqInv(1.0 * N / sq(m))
      (n :: n - 1 :: Nil) map (n => (m, n, sq(m) * sq(n)))
    }
    val rect = rects minBy (z => abs(z._3 - N))
    (rect._1 - 1) * (rect._2 - 1)
  }

  def p86(N: Int = 1000000) = {
    def tri(m: Int, n: Int, k: Int) =
      (
        k * (m * m - n * n),
        2 * k * m * n,
        k * (m * m + n * n))

    def sol(M: Int) = {
      val cubes = for {
        n <- (1 to M / 2).iterator
        m <- Iterator from n + 1 takeWhile { m =>
          val (a, b, _) = tri(m, n, 1)
          a <= 2 * M && b <= 2 * M
        }

        (k, t) <- Iterator from 1 map { k =>
          (k, tri(m, n, k))
        } takeWhile { case (_, (a, b, _)) => a <= 2 * M && b <= 2 * M }
        (a, b) <- (t._1, t._2) :: (t._2, t._1) :: Nil

        j <- 1 until b
        (x, y, z) = (a, j, b - j)
        if x >= y && y >= z && x <= M && y <= M && z <= M
      } yield (x, y, z)
      val distinct = cubes.toSet
      distinct.size
    }
  }

  def p87(N: Int = 50000000) = {
    val ps1 = primes(floor(pow(N, 1.0 / 2)).toInt + 1)
    val ps2 = primes(floor(pow(N, 1.0 / 3)).toInt + 1)
    val ps3 = primes(floor(pow(N, 1.0 / 4)).toInt + 1)

    val S = for {
      a <- ps1
      b <- ps2
      c <- ps3
      x = a * a + b * b * b + c * c * c * c
      if x < N
    } yield x

    S.toSet.size
  }

  def p88(N: Int = 12000) = {
    val D = mutable.Buffer.fill(N + 1)(Int.MaxValue)

    def f(k: Int, a: Int, m: Int): Iterator[List[Int]] = {
      if (k == 0)
        Iterator single Nil
      else
        for {
          x <- Iterator from a takeWhile (_ ** k <= m)
          ys <- f(k - 1, x, m / x)
        } yield x :: ys
    }

    val M = 2 * N
    val K = ilog(2, M)

    for {
      k <- 2 to K
      xs <- f(k, 2, M)
      n = xs.product
      k = n - xs.sum + xs.length
    } {
      if (k <= N)
        D(k) = min(D(k), n)
    }

    val ns = (D.iterator drop 2).toSet
    ns.sum
  }

  def p89(source: Source = getResource("roman.txt")) = {
    val pairs = Map(
      ('I', 'V') -> 4,
      ('I', 'X') -> 9,
      ('X', 'L') -> 40,
      ('X', 'C') -> 90,
      ('C', 'D') -> 400,
      ('C', 'M') -> 900)

    val value = Map(
      'I' -> 1,
      'V' -> 5,
      'X' -> 10,
      'L' -> 50,
      'C' -> 100,
      'D' -> 500,
      'M' -> 1000)

    def parse(xs: List[Char]): Int = {
      xs match {
        case Nil => 0
        case a :: b :: tl if (pairs contains (a, b)) => pairs((a, b)) + parse(tl)
        case a :: tl => value(a) + parse(tl)
      }
    }

    def repeat(s: String, n: Int): String = (List fill n)(s).mkString

    def repr(n: Int) = {
      val ks = split10(n).reverse padTo (4, 0)

      (ks(3) match {
        case 0 => ""
        case k @ _ => repeat("M", k)
      }) + (ks(2) match {
        case 0 => ""
        case k @ _ if k < 4 => repeat("C", k)
        case 4 => "CD"
        case k @ _ if k < 9 => "D" + repeat("C", k - 5)
        case 9 => "CM"
      }) + (ks(1) match {
        case 0 => ""
        case k @ _ if k < 4 => repeat("X", k)
        case 4 => "XL"
        case k @ _ if k < 9 => "L" + repeat("X", k - 5)
        case 9 => "XC"
      }) + (ks(0) match {
        case 0 => ""
        case k @ _ if k < 4 => repeat("I", k)
        case 4 => "IV"
        case k @ _ if k < 9 => "V" + repeat("I", k - 5)
        case 9 => "IX"
      })
    }

    (source.getLines map (line => line.length - repr(parse(line.toList)).length)).sum
  }

  def p90() = {
    val ps = ((0 to 9).toList combinations 6).toList

    val squares = List("01", "04", "06", "16", "25", "36", "46", "64", "81") map (s => (s(0) - '0', s(1) - '0'))

    def replace(xs: List[Int]) = xs map { x => if (x == 9) 6 else x }

    def ok(as2: List[Int], bs2: List[Int]) = {
      val as = replace(as2)
      val bs = replace(bs2)
      squares forall {
        case (x, y) =>
          (as contains x) && (bs contains y) || (as contains y) && (bs contains x)
      }
    }

    val ts = for {
      as :: bs :: Nil <- ps combinations 2
      if ok(as, bs)
    } yield (as, bs)
    ts.length
  }

  def p91(N: Int = 50) = {
    val ts = for {
      x <- 1 to N
      y <- 1 to N
    } yield {
      val d = gcd(x, y)
      min(y / (x / d), (N - x) / (y / d))
    }

    3 * N * N + ts.sum * 2
  }

  def p92(N: Int = 10000000) = {
    val chain = memoizeY(
      (n: Int, f: Int => Int) =>
        n match {
          case 1 => 1
          case 89 => 89
          case _ => f((split10(n) map (_ ** 2)).sum)
        })

    1 until N count (chain(_) == 89)
  }

  def p93(N: Int = 5) = {
    val eps = 1e-6

    val ops = List(
      (a: Double, b: Double) => Some(a + b),
      (a: Double, b: Double) => Some(a * b),
      (a: Double, b: Double) => Some(a - b),
      (a: Double, b: Double) => Some(b - a),
      (a: Double, b: Double) => if (b != 0 && (a % b < eps || a - (a % b) < eps)) Some(a / b) else None,
      (a: Double, b: Double) => if (a != 0 && (b % a < eps || b - (b % a) < eps)) Some(b / a) else None)

    def maxSeq(ns: List[Int]) = {
      val ys = for {
        ps <- ns.permutations
        op1 <- ops
        op2 <- ops
        op3 <- ops

        z1 = for {
          a <- op1(ps(0), ps(1))
          b <- op2(a, ps(2))
          c <- op3(b, ps(3))
          if c >= 1 && abs(c - round(c)) < eps
        } yield round(c)

        z2 = for {
          a <- op1(ps(0), ps(1))
          b <- op2(ps(2), ps(3))
          c <- op3(a, b)
          if c >= 1 && abs(c - round(c)) < eps
        } yield round(c)

        y <- z1.toList ::: z2.toList
      } yield y

      val zs = (SortedSet[Long]() ++ ys).iterator.zipWithIndex takeWhile { case (y, ix) => y == ix + 1 }
      zs.length
    }

    val ns = (1 to 9).toList combinations 4 maxBy maxSeq
    ns.mkString
  }

  def p94(N: Int = 1000000000) = {
    def isSquare(x: Long) = isqrt(x) ** 2L == x

    val ps = (Iterator from 2
      takeWhile (_ <= (N - 1) / 3)
      map { _.toLong }
      filter { _ % 2 == 1 }
      filter { c =>
        val b = (c + 1) / 2
        isSquare(c * c - b * b)
      } map (3 * _ + 1))

    val qs = (Iterator from 2
      takeWhile (_ <= (N + 1) / 3)
      map { _.toLong }
      filter { _ % 2 == 1 }
      filter { c =>
        val b = (c - 1) / 2
        isSquare(c * c - b * b)
      } map (3 * _ - 1))

    (ps ++ qs).sum
  }

  def p95(N: Int = 1000000) = {
    val M = mutable.Buffer.fill(N + 1)(-1)
    for (n <- 1 to N) {
      val s = sigmaProper(n, 1)
      if (s <= N)
        M(n) = s.toInt
    }

    def chainLength(n: Int) = {
      val xs = mutable.Set[Int]()
      def f(x: Int): Option[Int] = {
        if (x == -1)
          None
        else if (x == n)
          Some(0)
        else if (xs contains x)
          None
        else {
          val m = M(x)
          xs += x
          f(m) map (_ + 1)
        }
      }

      f(M(n)) map (_ + 1)
    }

    1 to N maxBy chainLength
  }

  def p96(source: Source = getResource("sudoku.txt")) = Problem096(source)

  object Problem096 {
    val M = 9

    case class DeadException() extends Exception("dead")

    object Sudoku {
      def apply(): Sudoku = Sudoku(
        mutable.Buffer.fill(M * M)(mutable.BitSet(0 until M: _*)),
        mutable.BitSet(0 until M * M: _*))
    }

    case class Sudoku(
      val xs: mutable.Buffer[mutable.BitSet],
      val qs: mutable.BitSet) {

      override def clone(): Sudoku =
        Sudoku(xs map (_.clone), qs.clone)

      def v(p: Int): Iterator[Int] = {
        val (i, j) = divide(p, M)
        (0 until M).iterator map (M * _ + j)
      }

      def h(p: Int): Iterator[Int] = {
        val (i, j) = divide(p, M)
        (0 until M).iterator map (M * i + _)
      }

      def s(p: Int): Iterator[Int] = {
        val (i, j) = divide(p, M)
        val (a, b) = (i / 3, j / 3)

        val ps = List.tabulate(3, 3) { case (x, y) => M * (3 * a + x) + 3 * b + y }
        ps.flatten.iterator
      }

      def restrict(p: Int, k: Int) = {
        val ks = xs(p)
        ks -= k
        if (ks.size == 0)
          throw new DeadException
      }

      def set(p: Int, k: Int) = {
        for (q <- v(p) ++ h(p) ++ s(p))
          if (q != p)
            restrict(q, k)

        for (z <- xs(p).toList)
          if (z != k)
            xs(p) -= z
        qs -= p
      }

      def simplify() = {
        var qsize = -1
        while (qsize != qs.size) {
          qsize = qs.size
          for (q <- qs) {
            val ks = xs(q)
            if (ks.size == 0)
              throw new DeadException
            if (ks.size == 1)
              set(q, ks.head)
          }
        }
      }

      def solve(): Sudoku = {
        simplify()
        if (qs.size == 0)
          this
        else {
          val rs = for {
            p <- qs.iterator
            ks = xs(p)
            if ks.size != 1
            k <- ks

            t <- try {
              val t = clone()
              t.set(p, k)
              Some(t.solve())
            } catch {
              case _: DeadException =>
                restrict(p, k)
                simplify()
                None
            }
          } yield t
          rs.next
        }
      }
    }

    def apply(source: Source) = {
      val N = 50

      val ts = for (zs <- source.getLines grouped M + 1) yield {
        val s = Sudoku()
        val xs = (zs drop 1).flatten map (_ - '1')
        for ((k, p) <- xs.zipWithIndex) {
          if (k != -1)
            s.set(p, k)
        }
        val t = s.solve()
        join10(t.xs take 3 map (_.head + 1))
      }

      ts.sum
    }
  }

  def p97() = {
    val N = 10
    val a = BigInt(28433)
    val e = BigInt(7830457)
    val n = BigInt(10L ** N)
    (a * powmod(BigInt(2), e, n) + 1) % n
  }

  def p98(source: Source = getResource("words.txt")) = {
    val isSquare = memoize((x: Int) => isqrt(x) ** 2 == x)
    def score = memoize((z: (List[Int], List[Int])) => {
      val (xs, ys) = z
      val c = xs.distinct.length
      val ts = for {
        cs <- (0 to 9) combinations c
        ds <- cs.permutations
        as = xs map ds
        bs = ys map ds
        if as(0) != 0 && bs(0) != 0
        a = join10(as)
        b = join10(bs)
        if isSquare(a) && isSquare(b)
      } yield max(a, b)
      if (ts.hasNext) Some(ts.max) else None
    })

    val wordr = "\"(\\w+)\"".r
    val words = (wordr findAllIn source.mkString map { case wordr(word) => word }).toList
    val gs = words groupBy (_.sorted)

    val ts = for {
      (_, g) <- gs
      w1 :: w2 :: Nil <- g combinations 2
      p1 = Permutation.cauchy(w1.distinct, w1)
      p2 = Permutation.cauchy(w1.distinct, w2)
      t <- score(p1, p2)
    } yield t

    ts.max
  }

  def p99(source: Source = getResource("base_exp.txt")) = {
    val bes = source.getLines map { line =>
      val parts = line split ','
      (parts(0).toInt, parts(1).toInt)
    }

    val t = bes.zipWithIndex maxBy { case ((b, e), _) => e * log(b.toDouble) }
    t._2 + 1
  }

  def p100(N: BigInt = BigInt(1000000000000L)) = {
    val xys = generalPellIterator(2, -1)
    val abs = xys map { case (x, y) => ((y + 1) / 2, (x + 1) / 2) }

    (abs find { case (x, y) => y > N }).get._1
  }

  def p101(ks: List[Double] = List(1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1)) = {
    def poly(ks: Seq[Double])(x: Double) =
      (ks.zipWithIndex map { case (k, i) => k * pow(x, i) }).sum

    def f = poly(ks)(_)
    val xys = 1 to ks.length map (i => (i.toDouble, f(i)))

    val eps = 1e-8
    val ts = 1 until ks.length map { k =>
      val g = lagrangeInterpolation(xys take k)
      val j = Iterator from k find (j => abs(f(j) - g(j)) > eps)
      round(g(j.get)).toLong
    }
    ts.sum
  }

  def p102(source: Source = getResource("triangles.txt")) = {
    val pss = source.getLines map { line =>
      val zs = line split ',' map (_.toInt)
      List(Vec2i(zs(0), zs(1)), Vec2i(zs(2), zs(3)), Vec2i(zs(4), zs(5)))
    }

    (pss filter { ps =>
      val x = Vec2i(0, 0)
      inside(ps, x) || inside(ps.reverse, x)
    }).length
  }

  def p103() = {
    def search(xs: List[Int]) =
      for {
        ds <- ndIndex(List.fill(xs.length)(7))
        ys = (xs zip ds map { case (x, d) => x + d - 5 }).sorted
        if ys.toSet.size == xs.length
        if Problem103.specialSum(ys)
      } yield ys

    val xs = List(11, 17, 20, 22, 23, 24)
    val mid = xs(xs.length / 2)
    val ys = mid :: (xs map (_ + mid))

    val zs = search(ys) minBy (_.sum)
    zs.mkString
  }

  object Problem103 {
    def specialSum(xs: List[Int]) = {
      val sets = (0 to (xs.length / 2)) map {
        i => SortedSet[Int]() ++ (xs combinations i map (_.sum))
      }
      ((sets sliding 2 forall { ys => ys(0).max < ys(1).min })
        && (sets.zipWithIndex forall { case (set, j) => set.size == ncr(xs.length, j) })
        && sets.last.max < xs.sum - sets((xs.length - 1) / 2).max)
    }
  }

  def p104() = {
    val phi = (1 + sqrt(5)) / 2
    def pandigital(xs: TraversableOnce[Int]) = xs.toList.sorted == (1 to 9).toList
    val t = fibonacciIterator.zipWithIndex drop 50 find {
      case (x, k) =>
        val m = floor(k * log10(phi) - log10(sqrt(5))).toInt + 1
        val head = x / BigInt(10).pow(m - 9)
        val tail = x mod 1000000000
        pandigital(split10(head)) && pandigital(split10(tail))
    }
    t.get._2
  }

  def p105(source: Source = getResource("sets.txt")) = {
    val sets = source.getLines map { line =>
      (line split ',' map (_.toInt)).toList
    }

    val ts = sets filter Problem103.specialSum
    (ts map (_.sum)).sum
  }

  def p106(N: Int = 12) =
    ((1 to N / 2) map { i => ncr(N, 2 * i) * (ncr(2 * i, i) / 2 - catalan(i)) }).sum

  def p107(source: Source = getResource("network.txt")) = {
    val D = (source.getLines map { line =>
      (line split ',' map (s => if (s == "-") Int.MaxValue else s.toInt)).toIndexedSeq
    }).toIndexedSeq

    def G(u: Int) = D(u).iterator.zipWithIndex filterNot (_._1 == Int.MaxValue) map (_._2)

    val path = prim(G, 0, (u: Int, v: Int) => D(u)(v))
    val newCost = (path map { case (u, v) => D(u)(v) }).sum
    val origCost = (D.flatten filter (_ != Int.MaxValue)).sum / 2
    origCost - newCost
  }

  def p108(N: Int = 1000) =
    (Iterator from 1 find { x =>
      val fs = factor(x)
      val d = (fs groupBy identity map { case (p, ks) => 2 * ks.length + 1 }).product
      (d + 1) / 2 > N
    }).get

  def p109(N: Int = 100) = {
    val rs = ((1 to 20 flatMap { r => r :: (2 * r) :: (3 * r) :: Nil })
      ++ (0 :: 25 :: 50 :: Nil))
    val ds = (1 to 20 map (2 * _)) :+ 50
    val ts = for {
      ai <- 0 until rs.length
      bi <- ai until rs.length
      a = rs(ai)
      b = rs(bi)
      c <- ds
    } yield a + b + c
    (ts filter (_ < N)).length
  }

  def p110(N: Int = 8000000) = {
    val ps = primes(100).toList

    val jMax = 2 * ceil(log(N) / log(2) / 2).toInt + 1
    def search(j: Int, n: Double): Iterator[List[Int]] =
      if (j > jMax)
        Iterator.empty
      else if (n < 1)
        Iterator single Nil
      else {
        val kmax = ceil(log(n) / log(j)).toInt
        val kmin = if (kmax == 1) 1 else 0
        for {
          k <- (kmin to kmax).iterator
          qs <- search(j + 2, n / pow(j, k))
        } yield (List fill k)(j) ::: qs
      }

    def eval(qs: List[Int]) =
      (qs.reverse zip ps map { case (q, p) => BigInt(p) pow ((q - 1) / 2) }).product

    val zs = search(3, N) map { qs => (qs, eval(qs)) }
    (zs minBy (_._2))._2
  }

  def p111(N: Int = 10) = {
    val ps = longPrimesRaw(10L ** N)
    def f(n: Int, d: Int) = {
      def merge(k: Int, ks: List[Int], ds: List[Int]): List[Int] = {
        if (ks == Nil && ds == Nil)
          Nil
        else if (ks != Nil && k == ks.head)
          d :: merge(k + 1, ks.tail, ds)
        else
          ds.head :: merge(k + 1, ks, ds.tail)
      }

      val xs = Iterator from 0 map (n - _) map {
        m =>
          for {
            ks <- (0 until n).toList combinations m
            ds <- ndIndex((List fill (n - m))(10))
            cs = merge(0, ks, ds)
            if cs(0) != 0
            x = joinBase[Long](10, cs)
            if !(ps get x)
          } yield x
      } find (!_.isEmpty)
      xs.get
    }

    (0 to 9 flatMap (f(N, _))).sum
  }

  def p112(N: Int = 99) = {
    def isBouncy(x: Int) = {
      val cs = split10(x)
      val ds = cs.sorted
      !(cs == ds || cs == ds.reverse)
    }

    val ts = (Iterator iterate (0, 0)) {
      case (n, d) =>
        (n + (if (isBouncy(d + 1)) 1 else 0), d + 1)
    }

    ts drop 1 find { case (n, d) => 100 * n == N * d }
  }

  def p113(N: Int = 100) =
    (1 to N map { n =>
      ncr(n + 9 - 1, 9 - 1) + ncr(n + 10 - 1, 10 - 1) - 9 - 1
    }).sum

  def p114(N: Int = 50, m: Int = 3) = {
    val f = memoizeY((n: Int, f: Int => BigInt) => {
      if (n < 0)
        BigInt(0)
      else if (n == 0)
        BigInt(1)
      else
        ((m + 1) to n map (k => f(n - k))).sum + f(n - 1) + (if (n >= m) 1 else 0)
    })
    f(N)
  }

  def p115(N: Int = 1000000, m: Int = 50) =
    (Iterator from 0 find { n => p114(n, m) > N }).get

  def p116(N: Int = 50) = {
    def f(m: Int) = memoizeY((n: Int, f: Int => BigInt) => {
      if (n < 0)
        BigInt(0)
      else if (n == 0)
        BigInt(1)
      else
        f(n - m) + f(n - 1)
    })

    val f2 = f(2)
    val f3 = f(3)
    val f4 = f(4)
    f2(N) + f3(N) + f4(N) - 1 - 1 - 1
  }

  def p117(N: Int = 50) = {
    val f = memoizeY((n: Int, f: Int => BigInt) => {
      if (n < 0)
        BigInt(0)
      else if (n == 0)
        BigInt(1)
      else
        f(n - 1) + f(n - 2) + f(n - 3) + f(n - 4)
    })
    f(N)
  }

  def p118() = {
    val e8 = 100000000
    val ps = longPrimesRaw(e8)

    def setPartitions(cs: List[Int]): Iterator[List[Int]] =
      cs match {
        case Nil =>
          Iterator single Nil
        case hd :: tl =>
          for {
            k <- (0 to tl.length).iterator
            as <- tl combinations k map (hd :: _)
            a <- as.permutations map join10
            if a < e8 && !(ps get a)
            bs <- setPartitions(cs filterNot (as contains _))
          } yield a :: bs
      }

    setPartitions((1 to 9).toList).length
  }

  def p119(N: Int = 30) = {
    val M = 10L ** 14
    val eps = 1e-8

    val qs = SortedSet[Long]() ++ (for {
      b <- Iterator from 2 takeWhile {
        b => b <= 9 * ceil(log(M.toDouble) / log(b)) * ceil(log10(b))
      }
      e <- 1 to ceil(log(M.toDouble) / log(b)).toInt
      x = b.toLong ** e
      if x >= 10 && b == split10(x).sum
    } yield x)

    (qs.iterator drop (N - 1)).next
  }

  def p120(N: Int = 1000) =
    (3 to N map { a =>
      a % 2 match {
        case 0 => a * (a - 2)
        case 1 => a * (a - 1)
      }
    }).sum

  def p121(N: Int = 15) = {
    val xss = (Iterator iterate List(BigInt(1), BigInt(1))) {
      xs =>
        val n = xs.length
        (BigInt(0) :: xs).zipAll(xs, BigInt(0), BigInt(0)) map {
          case (a, b) => a + n * b
        }
    }

    val xs = (xss drop (N - 1)).next
    val a = (xs drop ((N / 2) + 1)).sum
    val b = factorial(N + 1)
    b / a
  }

  def p122(N: Int = 200) = {
    def bySquares(n: Int): Int = {
      if (n <= 1)
        0
      else
        bySquares(n / 2) + (n % 2) + 1
    }

    val g = (Array tabulate (N + 1))(bySquares)

    def f(xs: List[Int], len: Int): Iterator[(Int, Int)] =
      (Iterator single (xs.head, len)) ++
        (for {
          a <- xs.iterator
          b = xs.head
          c = a + b
          if c <= N && len + 1 <= g(c)
          w <- f(c :: xs, len + 1)
        } yield w)

    val m = mutable.Map.empty[Int, Int] withDefaultValue Int.MaxValue
    for ((n, len) <- f(1 :: Nil, 0))
      m(n) = min(m(n), len)

    (1 to N map m).sum
  }

  def p123(N: Long = 10000000000L) = {
    val nEst = isqrt(N / 2) / sqrt(log(isqrt(N / 2)))
    val ps = primes((1.2 * pntInv(nEst)).toInt).toIndexedSeq
    def f(n: Int) = n % 2 match {
      case 0 => 2L
      case 1 =>
        val p = ps(n - 1).toLong
        (2L * n * p) % (p * p)
    }
    Iterator from 0 indexWhere (f(_) > N)
  }

  def p124(N: Int = 100000, M: Int = 10000) = {
    val xs = 1 to N map { n =>
      (factor(n).distinct.product, n)
    }

    val ys = xs.sorted
    ys(M - 1)._2
  }

  def p125(N: Int = 100000000) = {
    def isPalindrome(x: Int) = {
      val zs = split10(x)
      zs == zs.reverse
    }

    def g(n: Int) = n.toBigInt * (n + 1) * (2 * n + 1) / 6

    val ts = for {
      i <- (0 to isqrt(N)).iterator
      a = g(i)
      j <- Iterator from (i + 2) takeWhile (g(_) - a < N)
      b = g(j)
      c = b - a
      if isPalindrome(c.toInt)
    } yield c

    ts.toSet.sum
  }

  def p126(N: Int = 1000) = tunel()((M: Long) => {
    def f(a: Int, b: Int, c: Int, n: Int) =
      2 * (a * b + b * c + c * a) + 4 * n * (a + b + c) + 4 * n * (n - 1)

    val cs = for {
      a <- Iterator from 1 takeWhile (a => f(a, a, a, 0) <= M)
      b <- Iterator from a takeWhile (b => f(a, b, b, 0) <= M)
      c <- Iterator from b takeWhile (c => f(a, b, c, 0) <= M)
      n <- Iterator from 0 takeWhile (n => f(a, b, c, n) <= M)
    } yield f(a, b, c, n)

    val map = mutable.Map.empty[Int, Int] withDefaultValue 0
    for (c <- cs)
      map(c) += 1

    (map.view filter (_._2 == N) map (_._1)).to[SortedSet].headOption
  })

  def p127(N: Int = 120000) = {
    val rad = memoize((n: Int) =>
      (factor(n).distinct map (_.toLong)).product)

    val ts = for {
      a <- (1 until N).iterator
      ra = rad(a)
      c <- (a + a + 1) until N
      b = c - a
      if ra * rad(b) < c && gcd(a, b) == 1 && ra * rad(b) * rad(c) < c
    } yield c.toLong

    ts.sum
  }

  def p128(N: Int = 2000) = {
    type Pt = (Int, Int)
    val M = 1000000
    val ps = primes(M).toSet

    val ts = for {
      n <- Iterator from 1
      k <- 0 :: 6 * n - 1 :: Nil
      qs = k match {
        case 0 => 6 * n - 1 :: 6 * n + 1 :: 12 * n + 5 :: Nil
        case _ => 6 * n - 1 :: 6 * n + 5 :: 12 * n - 7 :: Nil
      }
      if qs forall (ps contains _)
    } yield centerHex(n) + k

    (ts map (_ + 1) drop N).next
  }

  def p129(N: Int = 1000000) =
    (Iterator from N filter (gcd(_, 10) == 1) find (Problem129.minExp(_) > N)).get

  object Problem129 {
    def minExp(x: Int) = {
      val qs = (Iterator iterate 1) { r => (10 * r + 1) % x }
      qs drop 1 indexWhere (_ == 1)
    }
  }

  def p130(N: Int = 25) = {
    val M = 100000

    val ps = primes(M).toSet
    val qs = (Iterator from 2
      filterNot (ps contains _)
      filter (gcd(_, 10) == 1)
      filter (n => (n - 1) % Problem129.minExp(n) == 0))
    (qs take N).sum
  }

  def p131(N: Int = 1000000) = {
    val ps = primes(N).toSet
    val rs = Iterator from 0 map centerHex takeWhile (_ < N) filter (ps contains _.toInt)
    rs.length
  }

  def p132(N: Int = 1000000000, L: Int = 40) = tunel()(M => {
    val ps = primes(M.toInt)
    val ts = ps filterNot (p => p == 2 || p == 5) filter { p =>
      val q = Problem129.minExp(p)
      N % q == 0
    }

    if (ts.length >= L)
      Some((ts take L).sum)
    else
      None
  })

  def p133(N: Int = 100000) = {
    val ps = primes(N)
    val ts = ps filterNot { p =>
      if (p == 2 || p == 5)
        false
      else {
        val q = Problem129.minExp(p)
        factor2(q) forall {
          case (a, k) =>
            a == 2 || a == 5
        }
      }
    }
    ts.sum
  }

  def p134(N: Int = 1000000) = {
    def f(p1: Long, p2: Long) = {
      val z = 10L ** ceil(log10(p1)).toInt
      val (s, t, _) = euclid(z, p2)
      divide(-s * p1, p2)._2 * z + p1
    }

    val ps = primes(N + 100)
    val p12s = ps drop 2 sliding 2 map (_.toList) takeWhile (_.head < N)
    (p12s map {
      qs =>
        val p1 :: p2 :: Nil = qs
        f(p1, p2).toBigInt
    }).sum
  }

  def p135(N: Int = 1000000, M: Int = 10) = {
    val ns = for {
      x <- (1 until N).iterator
      y <- 1 to min(3 * x - 1, (N - 1) / x)
      if (x + y) % 4 == 0
    } yield x * y

    val D = mutable.Map.empty[Int, Int] withDefaultValue 0
    for (n <- ns)
      D(n) += 1

    D count (_._2 == M)
  }

  def p136(N: Int = 50000000) = p135(N, 1)

  def p136b(N: Int = 50000000) {
    def f(n: Int) = {
      if (n % 4 == 2)
        false
      else {
        val fs = factor2(n)
        val ds = divisors(fs)
        val sqrtn = isqrt(n)
        val qs = ds filter (_ <= sqrtn) filter (d => d % 4 == (n / d) % 4)
        qs.hasNext && !(qs drop 1).hasNext
      }
    }

    (1 to N filter f).length
  }

  def p137(N: Int = 15) = {
    val xys = generalPellIterator(5, -4)
    val ts = xys filter (_._1 % 5 == 1) map { case (x, y) => (x - 1) / 5 }
    (ts drop N).next
  }

  def p138(N: Int = 12) = {
    val iters = List(
      pellIterator(5),
      generalPellIterator(5, -1))
    val xys = OrderedMergedIterator(iters)
    val tris = xys map { case (m, n) => pythagoreanTriple[BigInt](m + 2 * n, n, 1) }

    (tris take N map (_._3)).sum
  }

  def p139(N: Int = 100000000) = {
    val ts = for {
      m <- 1L to isqrt((N - 1) / 2)
      n <- 1L to min(m - 1, (N - 1) / (2 * m) - m)
      if (m - n) % 2 == 1 && gcd(m, n) == 1
      if (m * m + n * n) % (m * m - n * n - 2 * m * n) == 0
      p = 2 * m * (m + n)
    } yield (N - 1) / p
    ts.sum
  }

  def p140(N: Int = 30) = {
    val xys = generalPellIterator(5, 44)
    val ts = xys filter (_._1 % 5 == 2) map { case (x, y) => (x + 8) / 5 }
    val rs = ts map { _ - 3 } drop 1
    (rs take N).sum
  }

  def p141(N: Long = 1000000000000L) = {
    val squares = (Iterator from 1 map (x => x.toLong ** 2) takeWhile (_ < N)).toSet
    def f(s: Long, t: Long, k: Long) = k * t * (s * s * s * k + t)

    val ns = for {
      s <- Iterator from 1 takeWhile (f(_, 1, 1) < N)
      t <- 1 until s
      if gcd(s, t) == 1
      k <- Iterator from 1 takeWhile (f(s, t, _) < N)
    } yield f(s, t, k)
    (ns filter (squares contains _)).sum
  }

  def p142() = {
    val M = 1000L
    def f(m: Long, n: Long, p: Long, q: Long) = {
      val a = m * m + n * n - p * p - q * q
      val b = 2 * (m * q + n * p)
      val c = 2 * (n * q - m * p)
      (a, b, c)
    }

    val squares = (Iterator from 1 map (_.toLong ** 2) takeWhile (_ <= M * M)).toSet

    val abcsBruteForce = for {
      a <- Iterator from 1 map (_.toLong) takeWhile (a => a * a <= M * M)
      b <- Iterator from (a + 1).toInt map (_.toLong) takeWhile (b => a * a + b * b <= M * M)
      c <- (b + 1) to isqrt(M * M - a * a - b * b)
    } yield (a, b, c)

    // http://mathworld.wolfram.com/PythagoreanQuadruple.html
    val abcs = for {
      m <- Iterator from 0 map (_.toLong) takeWhile (m => m * m <= M)
      n <- Iterator from 0 map (_.toLong) takeWhile (n => m * m + n * n <= M)
      if gcd(m, n) == 1
      p <- Iterator from 0 map (_.toLong) takeWhile (p => m * m + n * n + p * p <= M)
      if gcd(m, p) == 1
      q <- 1L to isqrt(M - (m * m + n * n + p * p))
      if gcd(m, q) == 1 && (m + n + p + q) % 2 == 1

      (a, b, c) = f(m, n, p, q)
      if (a > 0 && b > 0 && c > 0)
    } yield (a, b, c)

    val ts = for {
      (a, b, c) <- abcs
      d2 = a * a + b * b + c * c
      if squares contains d2

      zs = IndexedSeq(a, b, c).sorted
      ys = 0 until 3 map { i => squares contains (zs(i) * zs(i) + zs((i + 1) % 3) * zs((i + 1) % 3)) }
      if (ys count identity) == 2

      j = ys indexWhere (_ == false)
      (ta, tb, tc) = j match {
        case 0 => (zs(1), zs(2), zs(0))
        case 1 => (zs(2), zs(0), zs(1))
        case 2 => (zs(2), zs(1), zs(0))
      }
      if (ta * ta - tc * tc) % 2 == 0
    } yield (ta, tb, tc, isqrt(d2))

    (ts map {
      case (a, b, c, d) =>
        d * d + (a * a - c * c) / 2
    }).min
  }

  def p143(N: Long = 120000L) = {
    val xyz0 = (1L, 0L, 1L)
    val f = diophantine2((1, 1, 1, 1), xyz0)(_, _)

    val xys = for {
      v <- (1L to floor(sqrt(N.toDouble / 3) - 1).toLong).iterator
      u <- (v + 1) to isqrt(N - 2 * v * v - 1)
      if gcd(u, v) == 1
      (px, py, _) = f(u, v)
      k <- 1L to (N / (px + py))
      (x, y) = (k * px, k * py)
    } yield if (x < y) (x, y) else (y, x)

    val m = mutable.Map.empty[Long, Set[Long]] withDefaultValue Set.empty
    for ((x, y) <- xys)
      m(y) += x

    val ts = for {
      (r, qs) <- m.iterator
      q <- qs
      p <- m(q)
      if (p + q + r <= N)
      if (qs contains p)
    } yield ((p, q, r))

    (ts map { case (p, q, r) => p + q + r }).toSet.sum
  }

  def p144() = {
    def eps = 1e-7

    val ps = (Iterator iterate (Vec2(0, 10.1), Vec2(1.4, -9.6))) {
      case (p, q) =>
        val r = 2 *: ((q - p) rej Vec2(4 * q.x, q.y)) + p
        val m = (r - q).slope
        val sopt = (for {
          x <- quadratic(m * m + 4, 2 * m * (q.y - m * q.x), m * m * q.x * q.x + q.y * q.y - 2 * q.x * q.y * m - 100)
          y <- quadratic(1, 0, 4 * x * x - 100)
        } yield Vec2(x, y)) find (s => (s - q).norm > eps && abs((s - q) det (r - q)) < eps)
        (q, sopt.get)
    }

    ps map (_._2) indexWhere { q => q.y > 0 && abs(q.x) <= 0.01 }
  }

  // very slow, 2946s
  def p145(N: Long = 1000000000L) = {
    (1L until N).iterator filter (_ % 10 != 0) count { n =>
      val m = joinBase[Long](10, split10(n).reverse)
      split10(m + n) forall (_ % 2 == 1)
    }
  }

  def p146(N: Long = 150000000) = {
    val is = List(1, 3, 7, 9, 13, 27)
    val js = List(15, 21, 23)

    val M = 100
    val ps = primes(M).toList
    def isNearPrime(n: Long) = ps takeWhile (p => p * p <= n) forall (n % _ != 0)

    val ts = for {
      x <- (10L until N by 10).iterator
      x2 = x ** 2
      if is map (x2 + _) forall isNearPrime
      if is map (x2 + _) map (BigInt(_)) forall millerRabin
      if js map (x2 + _) map (BigInt(_)) forall (!millerRabin(_))
    } yield x
    ts.sum
  }

  def p147(M: Int = 47, N: Int = 43) = {
    val f = memoizeY(
      (mn: (Int, Int), f: ((Int, Int)) => BigInt) => {
        val (m, n) = mn
        if (m == 1 && n == 1)
          BigInt(1)
        else if (m < n)
          f(n, m)
        else {
          val a = (1 to (2 * n - 1) map (k => (2 * n - k) * k) map (BigInt(_))).sum
          val b = n * (n + 1) / 2 * m
          val c = if (m == n) -n else 0
          a + b + c + f(m - 1, n)
        }
      })

    val g = memoizeY(
      (mn: (Int, Int), g: ((Int, Int)) => BigInt) => {
        val (m, n) = mn
        f(m, n) + (if (m > 1) g(m - 1, n) else 0) + (if (n > 1) g(m, n - 1) else 0) - (if (n > 1 && m > 1) g(m - 1, n - 1) else 0)
      })

    g(M, N)
  }

  def p148(N: Long = 1000000000) = {
    val p = 7
    def f(xs: List[Int], j: Int) = {
      val (ys, zs) = xs splitAt j
      (ys map (BigInt(_) + 1)).product * (zs.head * (zs.head + 1) / 2) * (p * (p + 1) / 2).toBigInt ** (zs.length - 1)
    }

    val xs = splitBase(7, N)
    (0 until xs.length map (f(xs, _))).sum
  }

  def p149(N: Int = 2000) = {
    val lfg = (lfgIterator take N * N map (_ - 500000)).toIndexedSeq

    def h(i: Int) = (0 until N).iterator map (i * N + _)
    def v(j: Int) = (0 until N).iterator map (_ * N + j)

    def d0(i: Int) =
      if (i > 0)
        (0 until (N - i)).iterator map (k => (i + k) * N + k)
      else
        (0 until (N + i)).iterator map (k => k * N - i + k)

    def d1(i: Int) =
      if (i < N)
        (0 to i).iterator map (k => (i - k) * N + k)
      else
        (0 until (2 * N - i - 1)).iterator map (k => (N - 1 - k) * N + (i - N + 1 + k))

    val lines = (0 until N map h).iterator ++
      (0 until N map v).iterator ++
      ((-N + 1) to (N - 1) map d0).iterator ++
      (0 to (2 * N - 2) map d1).iterator

    (lines map (line => maxSubarray(line map lfg))).max
  }

  def p150(N: Int = 1000) = {
    def partialSums(xs: Iterator[Long]) = {
      var s = 0L
      (Iterator single s) ++ (for (x <- xs) yield {
        s += x
        s
      })
    }

    val fs = lcg(1 << 20, 615949, 797807, 0) map (_ - (1 << 19))
    val gs = 0 to N map {
      i => partialSums(fs take i).toIndexedSeq
    }

    def minTriangleAt(i: Int, j: Int) = {
      val ts = (0 to (N - i)).iterator map {
        k => gs(i + k)(j + k) - gs(i + k)(j - 1)
      }
      (partialSums(ts) drop 1).min
    }

    (for {
      i <- (1 to N).iterator
      j <- 1 to i
    } yield minTriangleAt(i, j)).min
  }

  def p151() = {
    def cut(xs: List[Int], i: Int) =
      xs.zipWithIndex map {
        case (x, j) =>
          if (j < i) x + 1
          else if (j == i) x - 1
          else x
      }

    val Ms = ((Iterator iterate Map((List(0, 0, 0, 0, 1), 1.0))) {
      zs =>
        val M = mutable.Map.empty[List[Int], Double] withDefaultValue 0.0
        for {
          (xs, p) <- zs
          (x, i) <- xs.zipWithIndex
          sum = xs.sum
          if x > 0
        } M(cut(xs, i)) += x * p / sum
        M
    } take 16).toIndexedSeq

    val r = Ms(8)(List(0, 0, 0, 1, 0)) +
      Ms(12)(List(0, 0, 1, 0, 0)) +
      Ms(14)(List(0, 1, 0, 0, 0))

    "%.6f" format r
  }

  def p152(N: Int = 80) = {
    import Utils.Rational
    def excludeByPrime(p: Int) = {
      val qs = (1 to (N / p) map (_ * p)).toList
      val ts = for {
        rs <- subsets(qs)
        ts = rs map (k => Rational(1, k * k))
        t = (Rational(0, 1) /: ts)(_ + _)
        if t.b % p != 0
        t <- rs
      } yield t
      (SortedSet[Int]() ++ qs -- ts).toList
    }

    val ns = {
      val cs = 2 to N filter { n => n <= N / 2 || !isPrime(n) }
      val ds = for {
        p <- 5 to (N / 2) filter isPrime
        q <- excludeByPrime(p)
      } yield q
      (SortedSet[Int]() ++ cs -- ds).toIndexedSeq
    }

    val B = ns.length
    val A = ns.length / 2

    def partialSums(xs: Seq[Rational]) = {
      var s = Rational(0, 1)
      s +: (for (x <- xs) yield {
        s += x
        s
      })
    }

    val H = {
      val la = {
        val zs = A until B map (i => Rational(1, ns(i) * ns(i)))
        Rational(1, 2) - (Rational(0, 1) /: zs) { _ + _ }
      }
      val lb = Rational(1, 2)

      val sums = partialSums((0 until A).reverse map (i => Rational(1, ns(i) * ns(i)))).reverse.toIndexedSeq

      def f(x: Rational, ps: BitSet, j: Int): Iterator[(Rational, BitSet)] = {
        (Iterator single (x, ps)) ++ (for {
          (i, x2) <- (j until A).iterator map {
            i => (i, x + Rational.exact(1, ns(i) * ns(i)))
          } dropWhile (z => !(z._2 <= lb)) takeWhile (z => la <= z._2 + sums(z._1 + 1))
          y <- f(x2, ps + ns(i), i + 1)
        } yield y)
      }

      val zs = f(Rational(0, 1), BitSet.empty, 0) filter {
        case (x, ps) => la <= x && x <= lb
      }

      val H = mutable.Map.empty[Rational, List[BitSet]] withDefaultValue Nil
      for ((x, ps) <- zs)
        H(Rational(1, 2) - x) ::= ps
      H
    }

    val ts = {
      def f(x: Rational, ps: BitSet, j: Int): Iterator[(Rational, BitSet)] = {
        (Iterator single (x, ps)) ++ (for {
          i <- (j until B).iterator
          y <- f(x + Rational.exact(1, ns(i) * ns(i)), ps + ns(i), i + 1)
        } yield y)
      }

      for {
        (x, ps) <- f(Rational(0, 1), BitSet.empty, A)
        qs <- H(x)
      } yield qs ++ ps
    }

    ts.length
  }

  def p153(N: Long = 100000000) = {
    def f(n: Long) =
      ((1L to isqrt(n)).iterator map {
        k => (n / k) * k + (if (k != n / k) k * (nc2(n / k + 1) - nc2(n / (k + 1) + 1)) else 0)
      }).sum

    val ts = for {
      a <- (1L to isqrt(N)).iterator
      b <- (a to isqrt(N)).iterator
      if gcd(a, b) == 1
    } yield (if (a == b) a else (a + b)) * 2 * f(N / (a * a + b * b))

    ts.sum + f(N)
  }

  def p154(N: Int = 200000) = {
    val M = 1000000000000L

    val count2 = {
      val logN = floor(log(N) / log(2)).toInt
      val es = 1 to logN map (2 ** _)
      0 to N map (x => (es map (x / _)).sum)
    }

    val count5 = {
      val logN = floor(log(N) / log(5)).toInt
      val es = 1 to logN map (5 ** _)
      0 to N map (x => (es map (x / _)).sum)
    }

    val (n2, n5) = (count2(N), count5(N))

    val ts = for {
      a <- (0 to N).par
      (a2, a5) = (count2(a), count5(a))
    } yield ((a to (N - a) / 2).iterator map {
      b =>
        val c = N - a - b
        val (c2, c5) = (count2(c), count5(c))
        val (b2, b5) = (count2(b), count5(b))
        if (n5 - (a5 + b5 + c5) >= 12 && n2 - (a2 + b2 + c2) >= 12) {
          if (a != b && b != c)
            6L
          else if (a != b || b != c)
            3L
          else
            1L
        } else
          0L
    }).sum

    ts.sum
  }

  def p155(N: Int = 18) = {
    import Utils.Rational
    val f = memoizeY(
      (n: Int, f: Int => Set[Rational]) => {
        if (n == 1)
          Set(Rational(60, 1))
        else {
          Set() ++ (for {
            i <- (1 to n / 2).iterator
            j = n - i
            y <- f(j).par
            x <- f(i)
            c <- x + y :: Rational(x.a * y.a, x.a * y.b + x.b * y.a) :: Nil
          } yield c)
        }
      })

    val cs = (Set.empty[Rational] /: (1 to N).iterator)(_ ++ f(_))
    cs.size
  }

  def p156() = {
    def g(x: Long, d: Int): Long = {
      val e = floor(log10(x)).toLong
      val t = 10L ** e
      val (q, r) = divide(x, t)
      if (e <= 0)
        if (x > d) 1 else 0
      else
        q * e * (10L ** (e - 1)) + (if (q > d) t else 0L) +
          g(r, d) + (if (q == d) r else 0L)
    }

    def f2(n: Long, d: Int) = g(n, d) - n + 1

    val m = 10L ** 11
    def search(d: Int) = {
      def f(x: Long) = f2(x, d)

      def next(a: Long) = {
        val as = split10(a)
        val n = as.length
        val in = as contains d

        val uvs = 0 to 7 map {
          e =>
            val t = 10L ** e
            val (q, r) = divide(a - d * t, 10 * t)
            val u = (q + 1) * (10 * t) + d * t
            val v = u + t

            val cs = split10(u)
            val i = cs indexOf d
            val e2 = cs.length - i - 1
            val t2 = 10L ** e2
            val u2 = (u / t2) * t2
            val v2 = u2 + t2
            (u2, v2)
        }

        val fa = f(a)
        if (fa == 0)
          a + 1
        else if (in) {
          val e = n - (as indexOf d) - 1
          val t = 10L ** e
          val b = ((a / t) + 1) * t
          if (fa > 0)
            b
          else
            leastUpperBoundLong(f, a, b)(0)
        } else if (!in && fa < 0) {
          uvs find (z => f(z._2) >= 0) match {
            case Some((u, v)) => u
            case None => uvs.last._1
          }
        } else {
          val e = uvs indexWhere (z => f(z._1) <= 0)
          if (e == 0)
            a + 1
          else if (e == -1)
            uvs.last._2
          else
            uvs(e - 1)._2
        }
      }

      (Iterator iterate 1L)(next) takeWhile (_ < m) filter (f(_) == 0) map (_ - 1)
    }

    (for {
      i <- (1 to 9).par
      x <- search(i)
    } yield x).sum
  }

  def p157() = {
    def f(n: Int) = {
      val t = 10L ** n
      val rs = for {
        a2 <- (0 to n).iterator
        a = 2 ** a2
        b5 <- 0 to n
        b2 <- 0 to (if (a2 == 0 && b5 > 0) n - a2 else 0)
        b = (2 ** b2) * (5 ** b5)
        p = t / a / b * (a + b)
      } yield numDivisors(p)
      rs.sum
    }

    (1 to 9 map f).sum
  }

  def p158() = {
    def f(k: Int) = {
      val zs = (0 until k).toList combinations 2 collect {
        case a :: b :: Nil => BigInt(2) ** (b - a - 1)
      }
      ncr(26, k) * zs.sum
    }
    (1 to 26 map f).max
  }

  def p159(N: Int = 1000000) = {
    def digitalRoot(x: Int) =
      ((Iterator iterate x)(x => split10(x).sum) find (_ < 10)).get

    val partitions = memoize((xs: List[Int]) => multisetPartitions(xs).toList)

    def mdrs(x: Int) = {
      val fs = factor2(x)
      val ixs = (fs map (_._1)).toIndexedSeq
      val ds = for {
        qss <- partitions(fs map (_._2))
      } yield (qss map (_ map ixs.apply) map (_.product) map digitalRoot).sum
      ds.max
    }

    ((2 until N).par map mdrs).sum
  }

  def p160(N: Long = 1000000000000L) = {
    val m = 100000

    def d25(x: Long): (Int, Int, Long) =
      if (x % 2 == 0) {
        val (c2, c5, y) = d25(x / 2)
        (c2 + 1, c5, y)
      } else if (x % 5 == 0) {
        val (c2, c5, y) = d25(x / 5)
        (c2, c5 + 1, y)
      } else (0, 0, x)

    def prod(xs: Iterator[Long]): (Int, Int, Long) =
      ((0, 0, 1L) /: xs) {
        case ((s2, s5, p), x) =>
          val (c2, c5, y) = d25(x)
          (s2 + c2, s5 + c5, y * p % m)
      }

    def g(x: Long) =
      prod((1L to x).iterator filter { _ % 5 != 0 })

    val (m2, m5, mp) = g(m)

    def f(n: Long): (Long, Long, Long) = {
      if (n == 0)
        (0, 0, 1L)
      else {
        val (q, r) = divide(n, m)
        val (r2, r5, rp) = g(r)
        val (s2, s5, sp) = (q * m2, q * m5, powmod(mp, q, m))
        val (t2, t5, tp) = f(n / 5)
        (r2 + s2 + t2, r5 + s5 + t5 + n / 5, (rp * sp % m) * tp % m)
      }
    }

    val (t2, t5, tp) = f(N)
    powmod(2, t2 - t5, m) * tp % m
  }

  def p161(N: Int = 9, M: Int = 12) = {
    val pieces = List(
      List((0, 0), (1, 0), (0, 1)),
      List((0, 0), (0, 1), (1, 1)),
      List((0, 0), (1, 0), (1, 1)),
      List((0, 0), (1, 0), (1, -1)),
      List((0, 0), (1, 0), (2, 0)),
      List((0, 0), (0, 1), (0, 2)))

    def place(xs: BitSet, ab: (Int, Int), m: Int, piece: List[(Int, Int)]) = {
      val (a, b) = ab
      val inRange = piece forall { case (i, j) => 0 <= b + j && b + j < N && a + i < m }
      val qs = piece map { case (i, j) => (a + i) * N + b + j }
      if (inRange && (qs.toSet intersect xs).size == 0)
        Some(xs ++ qs)
      else
        None
    }

    def search(xs: BitSet): Iterator[BitSet] = {
      0 until N find (j => !(xs contains j)) match {
        case None => Iterator single xs
        case Some(j) => for {
          piece <- pieces.iterator
          ys <- place(xs, (0, j), 3, piece).iterator
          zs <- search(ys)
        } yield zs
      }
    }

    def complete(xs: BitSet): Iterator[BitSet] = {
      0 until 2 * N find (j => !(xs contains j)) match {
        case None => Iterator single xs
        case Some(j) => for {
          piece <- pieces.iterator
          ys <- place(xs, divide(j, N), 2, piece).iterator
          zs <- complete(ys)
        } yield zs
      }
    }

    val iter = memoize((xs: BitSet) => {
      val cs = mutable.Map.empty[BitSet, Int] withDefaultValue 0
      for (ys <- search(xs))
        cs(ys filter (_ >= N) map (_ - N)) += 1
      cs
    })

    val cs = ((Iterator iterate Map(BitSet() -> 1L)) {
      cs =>
        val ds = mutable.Map.empty[BitSet, Long] withDefaultValue 0L
        for {
          (xs, xc) <- cs
          (ys, yc) <- iter(xs)
        } ds(ys) += xc * yc
        ds
    } drop (M - 2)).next

    (for {
      (xs, xc) <- cs
      ys <- complete(xs)
    } yield xc).sum
  }

  def p162() = {
    def ipow(a: Int, b: Int) = a.toBigInt ** b
    def s16(b: Int) = ipow(b, 16 + 1) / (b - 1)

    val x = ipow(16, 16) - (s16(15) + 2 * ipow(15, 16)) + (2 * s16(14) + ipow(14, 16)) - s16(13)
    (splitBase(16, x) map { c =>
      if (c < 10) ('0' + c) else ('A' + (c - 10))
    } map (_.toChar)).mkString
  }

  def p163(N: Int = 36) = {
    def lines(n: Int, c: Int) = c match {
      case 0 =>
        0 until n map { i =>
          val a = Vec2i(2 * i, 6 * i)
          val d = (n - i) *: Vec2i(4, 0)
          (a, a + d)
        }
      case 1 =>
        0 until n map { i =>
          val a = Vec2i(4 * i, 0)
          val d = (n - i) *: Vec2i(2, 6)
          (a, a + d)
        }
      case 2 =>
        1 to n map { i =>
          val a = Vec2i(4 * i, 0)
          val d = i *: Vec2i(-2, 6)
          (a, a + d)
        }
      case 3 =>
        -(n - 1) to (n - 1) map { i =>
          val b = Vec2i(3 * n - i, 3 * n + 3 * i)
          val d = (n - abs(i)) *: Vec2i(3, 3)
          (b - d, b)
        }
      case 4 =>
        -(n - 1) to (n - 1) map { i =>
          val a = Vec2i(2 * n + 2 * i, 0)
          val d = (n - abs(i)) *: Vec2i(0, 6)
          (a, a + d)
        }
      case 5 =>
        -(n - 1) to (n - 1) map { i =>
          val b = Vec2i(n - i, 3 * n - 3 * i)
          val d = (n - abs(i)) *: Vec2i(-3, 3)
          (b - d, b)
        }
    }

    def countTriangles(n: Int) =
      for {
        c0 :: c1 :: c2 :: Nil <- (0 until 6).toList combinations 3
        a <- lines(n, c0)
        b <- lines(n, c1)
        c <- lines(n, c2)
        if xSegSeg(a._1, a._2, b._1, b._2)
        if xSegSeg(b._1, b._2, c._1, c._2)
        if xSegSeg(c._1, c._2, a._1, a._2)
      } yield (a, b, c)

    val collinear = N * N + 20 * (ncr(N + 2, 2) - 3) + 3
    countTriangles(N).length - collinear
  }

  // http://oeis.org/A210687
  def p163b(N: Int = 36) =
    (1678 * (N ** 3) + 3117 * (N ** 2) + 88 * N - 345 * (N % 2) - 320 * (N % 3) - 90 * (N % 4) - 288 * (((N ** 3) - (N ** 2) + N) % 5)) / 240

  def p164(N: Int = 20) = {
    def f(x: Int): Map[(Int, Int), Long] =
      if (x == 0)
        Map((0, 0) -> 1)
      else {
        val M = mutable.Map.empty[(Int, Int), Long] withDefaultValue 0L
        for {
          ((b, a), s) <- f(x - 1)
          c <- 0 to (9 - (a + b))
        } M((c, b)) += s
        M
      }

    (f(N) filter { case ((b, a), _) => b != 0 } map (_._2)).sum
  }

  def p165(N: Int = 5000) = {
    import Utils.Rational
    val ts = bbs(290797L, 50515093L) map (_ % 500)
    val ls = (ts drop 1 grouped 4 map {
      xs => (Vec2i(xs(0), xs(1)), Vec2i(xs(2), xs(3)))
    } take N).toIndexedSeq

    def xLineLine(a: Vec2i[Long], b: Vec2i[Long], c: Vec2i[Long], d: Vec2i[Long]) = {
      val p = (a det b) *: (c - d) - (c det d) *: (a - b)
      val z = (a - b) det (c - d)
      (Rational(p.x, z), Rational(p.y, z))
    }

    val rs = for {
      ((a, b), i) <- ls.zipWithIndex.par
      j <- i + 1 until ls.length
      (c, d) = ls(j)
      if xSegSegOpen(a, b, c, d)
    } yield xLineLine(a, b, c, d)
    rs.toSet.size
  }

  def p166() = {
    def isDigit(x: Int) = 0 <= x && x < 10
    val ts = for {
      x1 :: x2 :: x3 :: x4 :: x8 :: Nil <- ndIndex((List fill 5)(10))
      x12 = x1 + x2 + x3 - x4 - x8
      if isDigit(x12)
      x0 :: x6 :: Nil <- ndIndex((List fill 2)(10))
      s = x0 + x1 + x2 + x3
      x9 = s - (x3 + x6 + x12)
      if isDigit(x9)
      x5 <- 0 until 10
      x7 = s - (x4 + x5 + x6)
      if isDigit(x7)
      x13 = s - (x1 + x5 + x9)
      if isDigit(x13)
      x10 <- 0 until 10
      x11 = s - (x8 + x9 + x10)
      x14 = s - (x2 + x6 + x10)
      x15 = s - (x0 + x5 + x10)
      if isDigit(x11) && isDigit(x14) && isDigit(x15)
      if x12 + x13 + x14 + x15 == s && x3 + x7 + x11 + x15 == s
    } yield 1
    ts.length
  }

  def p167(N: Long = 100000000000L) = {
    def ulam2(b: Int) = {
      val a = 2

      case class Part1() extends Iterator[Int] {
        val C = mutable.BitSet(a + b)
        val D = mutable.BitSet()
        val L = mutable.BitSet(a, b)
        var even: Option[Int] = None

        def hasNext = even.isEmpty
        def next = {
          val x = C.head

          for (y <- L) {
            val z = x + y
            if (!D(z)) {
              if (!C(z))
                C += z
              else {
                C -= z
                D += z
              }
            }
          }
          C -= x
          L += x

          if (x % 2 == 0)
            even = Some(x)

          x
        }
      }

      case class Part2(even: Int, _C: Set[Int]) extends Iterator[Int] {
        val C = mutable.SortedSet[Int]() ++ (_C filter (_ % 2 != 0))
        val L = List(a, even)

        def hasNext = true
        def next = {
          val x = C.head
          for (y <- L) {
            val z = x + y
            if (!C(z))
              C += z
            else
              C -= z
          }
          C -= x
          x
        }
      }

      val part1 = Part1()
      lazy val part2 = Part2(part1.even.get, part1.C)
      List(a, b).iterator ++ part1 ++ part2
    }

    val rs = for (n <- (2 to 10).par) yield {
      val a = 2
      val b = 2 * n + 1

      val xs = ulam2(b).toStream
      val ds = xs zip (xs drop 1) map { case (a, b) => b - a }

      val (u, v) = {
        val k1 = 500
        val k2 = 25
        val zs = (ds drop k1 take k2).toIndexedSeq
        val v = (ds drop (k1 + 1) sliding k2 indexWhere (_ == zs)) + 1
        (k1, v)
      }
      val ys = ds drop u take v
      val ysum = ys.sum

      def f(k: Long) =
        if (k < u)
          xs(k.toInt)
        else {
          val (q, r) = divide(k - u, v)
          xs(u) + q * ysum + (ys take r.toInt).sum
        }
      f(N - 1)
    }
    rs.sum
  }

  def p168(N: Int = 100) = {
    import Utils.Rational
    val m = 10 ** 5
    val ts = for {
      e <- (1 until N).iterator
      k <- 1 to 9
      r = Rational(BigInt(10) ** e - k, 10 * k - 1)
      if r.b < 10

      ju = if (e == 1)
        1
      else
        (((BigInt(10) ** (e - 1)) + r.a) / r.a).toInt
      jv = 9 / r.b.toInt
      j <- ju to jv
    } yield 10 * j * r.a + j * r.b
    ts.sum % m
  }

  def p169(x: BigInt = BigInt(10) pow 25) = {
    def g(xs: List[Int]): List[Int] = xs match {
      case 0 :: tl =>
        val a :: as = g(tl)
        a + 1 :: as
      case 1 :: tl => 0 :: g(tl)
      case Nil => Nil
      case _ => Nil
    }

    val xs = splitBaseLe(2, x)
    val as = g(xs)

    val (u, v) = ((BigInt(1), BigInt(0)) /: as) {
      case ((u: BigInt, v: BigInt), a: Int) =>
        (u + v, a * u + (a + 1) * v)
    }
    u + v
  }

  // http://projecteuler.net/thread=169
  def p169b(x: BigInt = BigInt(10) pow 25) = {
    def f(x: BigInt): BigInt = {
      if (x == 0)
        1
      else if (x % 2 == 0)
        f(x / 2) + f(x / 2 - 1)
      else
        f((x - 1) / 2)
    }

    f(x)
  }

  def p170() = {
    import std.list._
    import syntax.traverse._
    type LInt = List[Int]
    type Z[A] = StateT[List, LInt, A]

    val ns = for {
      a <- (1 to 30).par
      as = split10(a)
      ps <- integerPartition(10 - as.length)
      if ps.length >= 2
      (_, bz :: czs) <- ps.traverse[Z, LInt](x => StateT(ds =>
        (ds combinations x map (es => (ds filterNot (es contains _), es))).toList))
        .apply((0 to 9 filterNot (as contains _)).toList)

      n <- {
        def g(cs: LInt) = split10(a * join10(cs))
        val D = mutable.Map.empty[LInt, mutable.Set[List[LInt]]] withDefault (_ => mutable.Set.empty[List[LInt]])
        for {
          css <- czs.traverse(cz => (cz.permutations filter {
            cs =>
              val ys = g(cs)
              cs.head != 0 && ys.toSet.size == ys.length
          }).toList)
          yss = css map g
          yz = yss.flatten
          if yz.length == yz.toSet.size
        } {
          val xz = (0 to 9 filterNot (yz contains _)).toList
          val ysss = D getOrElseUpdate (xz, mutable.Set.empty[List[LInt]])
          ysss += yss
        }

        for {
          bs <- bz.permutations
          if bs.head != 0
          xs = split10(a * join10(bs))
          yss <- D(xs.sorted)
        } yield joinBase[Long](10, (xs :: yss sortBy (-_.head)).flatten)
      }
    } yield n

    ns.max
  }

  def p171(N: Int = 20, M: Int = 9) = {
    val squares = (0 to (N * 9 * 9) map (_ ** 2)).toSet
    val ones = (10L ** M - 1) / (10 - 1)

    val ns = for {
      ds <- starsAndBars(10, N)
      if squares contains (ds.zipWithIndex map { case (c, d) => c * d * d }).sum
      p = multinomial(ds)
      (c, d) <- ds.zipWithIndex
    } yield p * c * d * ones / N

    ns.sum % (10L ** 9)
  }

  def p172(N: Int = 18) = {
    def starsAndBars3(n: Int, k: Int): Iterator[List[Int]] = {
      if (n == 0 && k == 0)
        Iterator single Nil
      else if (n == 0)
        Iterator.empty
      else if (n == 1 && k > 3)
        Iterator.empty
      else if (n == 1)
        Iterator single k :: Nil
      else
        for {
          a <- (0 to min(k, 3)).iterator
          bs <- starsAndBars3(n - 1, k - a)
        } yield a :: bs
    }

    val ps = for {
      ds <- starsAndBars3(10, N)
      p = multinomial(ds) - (if (ds.head != 0) multinomial(ds.head - 1 :: ds.tail) else 0)
    } yield p
    ps.sum
  }

  def p173(N: Int = 1000000) =
    (4 to N by 4 map (x => numDivisors(x / 4) / 2)).sum

  def p174(N: Int = 1000000) = {
    val M = mutable.Map.empty[Int, Int] withDefaultValue 0
    for {
      x <- 4 to N by 4
    } M(numDivisors(x / 4) / 2) += 1
    (1 to 10 map M).sum
  }

  def p175(p: Int = 123456789, q: Int = 987654321) = {
    def h(p: Int, q: Int): List[(Int, Int)] =
      if (q == 0)
        Nil
      else if (p <= q) {
        val (d, r) = divide(q, p)
        (d, 1) :: h(p, r)
      } else {
        val (d, r) = divide(p - 1, q)
        (d, 0) :: h(r + 1, q)
      }

    val ns = h(p, q).reverse
    ns map (_._1) mkString ","
  }

  def p176(N: Int = 47547) = {
    val d = 2 * N + 1
    val fs = factor(d).reverse
    val ps = primes(100)
    (ps take fs.length zip fs.iterator map { case (p, k) => p.toBigInt ** ((k - 1) / 2) }).product * 2
  }

  def p177() = {
    val sini = 0 to 180 map (x => sin(toRadians(x)))
    val cosi = 0 to 180 map (x => cos(toRadians(x)))
    val eps = 1e-9

    val ts = for {
      a <- (1 until 180).iterator
      b <- (a until 180 - a).par
      c <- 1 until 180 - a - b
      h = 180 - (a + b + c)
      f <- 1 until 180 - a - h
      v = sini(a + b) / sini(c)
      s = sini(a) / sini(f)
      g = 180 - (a + f + h)
      r = sqrt(v * v + s * s - 2 * s * v * cosi(g))
      d = toDegrees(atan2(2 * v * s * sini(g), v * v + r * r - s * s))
      if abs(d - round(d)) < eps
      di = round(d).toInt
      e = 180 - (b + c + di)
    } yield List(
      (a + b, min(a, b)),
      (c + di, min(c, di)),
      (e + f, min(e, f)),
      (g + h, min(g, h)))

    val ts2 = for {
      t <- ts
      i = (t.zipWithIndex maxBy (_._1))._2
      p :: q :: r :: s :: Nil = rotate(t, i)
    } yield if (q >= s)
      List(p, q, r, s)
    else
      List(p, s, r, q)

    ts2.toSet.size
  }

  def p178(N: Int = 40) = {
    def iter(D: Map[(Int, Int, Int), Long]) = {
      val E = for {
        u <- 0 to 9
        v <- u to 9
        d <- u to v
      } yield {
        val s = D(d - 1, u, v) + D(d + 1, u, v) +
          (if (d == v) D(d - 1, u, v - 1) else 0) +
          (if (d == u) D(d + 1, u + 1, v) else 0)
        ((d, u, v), s)
      }
      E.toMap withDefaultValue 0L
    }

    val D = (0 to 9 map (d => ((d, d, d), 1L))).toMap withDefaultValue 0L
    val Ds = (Iterator iterate D)(iter)

    val ts = for {
      D <- Ds take N
      d <- 1 to 9
    } yield D(d, 0, 9)
    ts.sum
  }

  // really slow 155s
  def p179(N: Int = 10000000) =
    (1 to N).iterator map (numDivisors(_)) sliding 2 count {
      x => x(0) == x(1)
    }

  def p180(k: Int = 35) = {
    import spire.math.Rational
    def isSquare(x: Long) = isqrt(x) ** 2 == x

    val ts = for {
      a <- (1 to k).iterator
      b <- (a + 1) to k
      c <- 1 to k
      d <- (c + 1) to k
      if a * d - b * c <= 0
      x = Rational(a, b)
      y = Rational(c, d)
      z <- {
        var L = List[Rational]()
        L ::= x + y
        L ::= x * y / (x + y)
        val w = a * a * d * d + b * b * c * c
        if (isSquare(w)) {
          L ::= Rational(isqrt(w), b * d)
          L ::= Rational(a * c, isqrt(w))
        }
        L
      }
      if 0 < z && z < 1 && z.denominator <= k
    } yield x + y + z

    val uv = ts.toSet.qsum
    uv.numerator + uv.denominator
  }

  def p181(a: Int = 60, b: Int = 40) = {
    val f = memoizeY((xvs: (List[Int], List[Int]), f: ((List[Int], List[Int])) => BigInt) => {
      val (a :: b :: Nil, av :: bv :: Nil) = xvs
      if (a == 0 && b == 0)
        BigInt(1)
      else {
        val ts = for {
          i <- (0 to min(a, av)).iterator
          j <- 0 to b
          if (i < av || j <= bv) && !(i == 0 && j == 0)
        } yield f(List(a - i, b - j), List(i, j))
        ts.sum
      }
    })

    f(List(a, b), List(a, b))
  }

  def p182(p: Long = 1009, q: Long = 3643) = {
    val n = p * q
    val φ = (p - 1) * (q - 1)

    val ts = (for {
      e <- (2L until φ).par
      if gcd(e, φ) == 1
      c = (gcd(e - 1, p - 1) + 1) * (gcd(e - 1, q - 1) + 1)
    } yield (e, c)).toMap

    val tmin = (ts.view map (_._2)).min
    (ts.view filter (_._2 == tmin) map (_._1)).sum
  }

  def p183(N: Int = 10000) = {
    def f(r: Int) = {
      val k = round(r / e).toInt
      factor(k / gcd(r, k)) forall (p => p == 2 || p == 5)
    }

    (5 to N map (r => if (f(r)) -r else r)).sum
  }

  def p184(r: Int = 105) = {
    val ps = (for {
      x <- 1 until r
      y <- 0 until isqrtCeil(r * r - x * x)
      if gcd(x, y) == 1
      k = ceil(r / sqrt(x * x + y * y)).toLong - 1L
    } yield ((x, y), k)) sortBy { case ((x, y), _) => 1.0 * y / x }

    val M = mutable.Map[(Int, Int), Long]()
    var mc = 0L
    for ((p, k) <- ps) {
      M(p) = mc
      mc += k
    }

    val ts = for {
      ((a, ak), ai) <- ps.zipWithIndex.iterator
      bi <- ai + 1 until ps.length
      (b, bk) = ps(bi)
    } yield (M(b) - M(a) - ak) * ak * bk

    val rs = for {
      (a, ak) <- ps.iterator
    } yield (mc - M(a) - ak) * mc * ak

    4 * ts.sum + 4 * rs.sum
  }

  def p185(data: String = StringData.s185) = {
    val r = "(\\d+) ;(\\d+) correct".r
    val clues0 = for {
      line <- data split "\n"
      if line != ""
    } yield {
      val r(zs, k) = line
      (zs map (_ - '0'), k.toInt)
    }
    val clues = clues0.toList sortBy (_._2)
    val N = clues.length
    val M = clues(0)._1.length

    val x0 = (Vector fill M)(BitSet() ++ (0 to 9))

    type Clue = (IndexedSeq[Int], Int)
    type S = IndexedSeq[BitSet]
    def f(x: S, clue: Clue, tl: List[Clue]) = {
      val (cs, k) = clue
      val js = cs.zipWithIndex filter (_._1 != -1) map (_._2)
      for {
        is <- js combinations k
        y = x.zipWithIndex map {
          case (ds, i) =>
            val c = cs(i)
            if (is contains i)
              ds & BitSet(c)
            else if (c != -1)
              ds - cs(i)
            else
              ds
        }
        if y forall (!_.isEmpty)
        tl2 = tl map {
          case (es, l) =>
            var l2 = l
            val fs = es.zipWithIndex map {
              case (e, i) =>
                if (is contains i) {
                  if (e == cs(i))
                    l2 -= 1
                  -1
                } else
                  e
            }
            (fs, l2)
        }
      } yield (y, tl2)
    }

    def search(x: S, clues: List[Clue], k: Int): Iterator[S] =
      clues match {
        case hd :: tl =>
          if (k == 3 || k == 4)
            (for {
              (y, tl2) <- f(x, hd, tl).toList.par
              z <- search(y, tl2, k + 1)
            } yield z).iterator
          else
            for {
              (y, tl2) <- f(x, hd, tl)
              z <- search(y, tl2, k + 1)
            } yield z
        case Nil => Iterator single x
      }

    val x = search(x0, clues, 0).next
    (x map (_.head)).mkString
  }

  def p186() = {
    val M = 1000000
    val P = (mutable.Buffer tabulate M)(identity)
    val R = (mutable.Buffer fill M)(0)
    val C = (mutable.Buffer fill M)(1)

    def union(a: Int, b: Int) = {
      val u = find(a)
      val v = find(b)
      if (u != v) {
        val (x, y) = if (R(u) <= R(v)) {
          if (R(u) == R(v))
            R(v) += 1
          (u, v)
        } else
          (v, u)
        P(x) = y
        C(y) += C(x)
        C(x) = 0
      }
    }

    def find(a: Int): Int = {
      val y = P(a)
      if (y == a)
        y
      else {
        val z = find(y)
        P(a) = z
        z
      }
    }

    val x0 = 524287
    val ts = for {
      Seq(a, b) <- lfgIterator grouped 2
      if (a != b)
      _ = union(a, b)
    } yield C(find(x0))

    (ts indexWhere (100 * _ >= 99 * M)) + 1
  }

  // really slow 290s
  def p187(N: Int = 100000000) = {
    def f(n: Int, k: Int = 2): Iterator[Int] =
      k to isqrt(n) find (n % _ == 0) match {
        case Some(p) =>
          (Iterator single p) ++ f(n / p, p)
        case None => Iterator single n
      }

    (2 until N).par count {
      x =>
        val fs = f(x)
        fs.next
        if (!fs.hasNext)
          false
        else {
          fs.next
          !fs.hasNext
        }
    }
  }

  def p188(a: Long = 1777, b: Long = 1855) = {
    val m = 100000000
    val powmod = powmodCached(a, m)
    def tet(b: Long): Long = {
      if (b == 1) a
      else powmod(tet(b - 1))
    }
    tet(b)
  }

  def p189(N: Int = 8) = {
    def iter(A: Map[List[Int], BigInt]) = {
      val M = A.head._1.length
      val B = mutable.Map[List[Int], BigInt]() withDefaultValue 0
      for {
        (as, ac) <- A.iterator
        is <- ndIndex((List fill M)(2))
        bs = is zip as map { case (i, a) => if (i >= a) i + 1 else i }
        js <- ndIndex(2 :: (List fill M)(2))
        cs = js zip (bs.head :: bs) map { case (j, b) => if (j >= b) j + 1 else j }
        if cs zipAll (bs, -1, -1) forall { case (c, b) => c != b }
      } B(cs) += ac
      B
    }

    val A0: Map[List[Int], BigInt] = (0 until 3 map (a => (List(a), BigInt(1)))).toMap
    val ts = (Iterator iterate A0)(iter)
    val t = (ts drop (N - 1)).next
    (t map (_._2)).sum
  }

  def p190(N: Int = 15) = {
    def f(m: Int) = {
      val ps = 1 to m map { k =>
        val x = 1.0 * k * m / nc2(m + 1)
        pow(x, k)
      }
      floor(ps.product).toLong
    }
    (2 to N map f).sum
  }

  def p191() = {
    def f(x: Int): List[Long] =
      if (x == 1)
        List(
          1, 1, 0,
          1, 0, 0)
      else {
        val a :: b :: c :: a1 :: b1 :: c1 :: Nil = f(x - 1)
        List(
          a + b + c, a, b,
          a + b + c + a1 + b1 + c1, a1, b1)
      }

    f(30).sum
  }

  def p192(N: Int = 100000, M: Long = 10L ** 12) = {
    def isSquare(x: Int) = isqrt(x) ** 2 == x

    val mc = new java.math.MathContext(100)
    val ts = for {
      n <- (1 to N).par
      if !isSquare(n)
      uvss = cfEvalWithSemiConvergents(sqrtCf(n) map { _._1 }) takeWhile (_.head._2 <= M)
      uvs0 :: uvs1 :: Nil = uvss.toList.reverse take 2
      (u, v) = (uvs1.last :: uvs0 takeWhile (_._2 <= M)) minBy { case (u, v) => abs(BigDecimal(u, mc) / BigDecimal(v, mc) - sqrt(BigDecimal(n, mc))) }
    } yield v
    ts.sum
  }

  def p193(N: Long = 2L ** 50) = {
    val N2 = isqrt(N)

    val ps = primes(N2.toInt).toIndexedSeq

    def g(k: Int, n: Long, u: Int): Iterator[List[Long]] =
      if (k == 0)
        Iterator single Nil
      else {
        val m = floor(pow(n, 1.0 / k)).toInt
        val v = leastStrictUpperBound(ps, 0, ps.length)(m)
        for {
          i <- (u until v).iterator
          x = ps(i)
          ys <- g(k - 1, n / x, i + 1)
        } yield x.toLong :: ys
      }

    def f(k: Int) =
      (g(k, N2, 0) map (xs => N / (xs.product ** 2))).sum

    val ts = (Iterator from 0 parMap f takeWhile (_ != 0)).zipWithIndex
    (ts map { case (t, k) => (if (k % 2 == 0) 1 else -1) * t }).sum
  }

  def p194(a: Int = 25, b: Int = 75, c: Long = 1984) = {
    val M = 10L ** 8
    def f(c: Long, mode: Int) = {
      // a == d, b == c
      val p = 1
      val q = (c - 2) * (c - 1) + (c - 2) * (c - 3) * (c - 2)
      (p % M) * (q % M) % M
    } + {
      // a != d, b != c
      val p = (c - 2) * (c - 3)
      val q = (c - 4) * (c - 1) + 2 * (c - 2) * (c - 2) + (c - 4) * (c - 3) * (c - 2)
      (p % M) * (q % M) % M
    } + {
      // a == d xor b == c
      val p = 2 * (c - 2)
      val q = ((c - 3) * (c - 1) + (c - 2) * (c - 2) + (c - 3) * (c - 3) * (c - 2))
      (p % M) * (q % M) % M
    } + (if (mode == 1) {
      // b == d
      val p = c - 2
      val q = (c - 1) * (c - 2) + (c - 3) * (c - 1) + (c - 3) * (c - 2) * (c - 2)
      (p % M) * (q % M) % M
    } else 0)

    val g = memoizeY(
      (ab: (Int, Int), g: Tuple2[Int, Int] => Long) => ab match {
        case (0, 0) => c * (c - 1)
        case (a, 0) => g(a - 1, 0) * f(c, 0) % M
        case (0, b) => g(0, b - 1) * f(c, 1) % M
        case (a, b) => (g(a - 1, b) * f(c, 0)) % M + (g(a, b - 1) * f(c, 1)) % M
      })
    g(a, b)
  }

  def p195(N: Int = 1053779) = {
    val xyz0 = (1L, 0L, 1L)
    val f = diophantine2((1, -1, 1, 1), xyz0)(_, _)

    val k0 = 3 // fudge factor
    val m = floor(k0 * 2 * N / sqrt(3)).toLong
    val ts = for {
      v <- (1L to m).iterator
      u <- (2 * v + 1 to m / v + v).iterator
      if gcd(u, v) == 1
      (za, zb, zc) = f(u, v)
      g = if ((u + v) % 3 == 0) 3 else 1
      (a, b, c) = (za / g, zb / g, zc / g)
      if a != b && b != c
      r = sqrt(3) / 2 * a * b / (a + b + c)
    } yield floor(N / r).toInt

    ts.sum
  }

  def p196(is: List[Long] = List(5678027, 7208785)) = {
    val ps = is.to[SortedSet] flatMap (i => primesRange(nc2(i - 2), nc2(i + 3)))
    def isPrime(z: Long) = ps contains (z.toLong)

    def toPt(p: Long) = {
      val i = nc2Invi(p - 1) + 1
      val j = p - nc2(i)
      (i, j)
    }

    val ds = (ndIndex(List(3, 3)) map (_ map (_ - 1)) filter (_ != List(0, 0))).toList
    def search1(i: Long, j: Long, path: List[Long]): Iterator[Unit] = {
      if (path.length == 3)
        Iterator single ()
      else
        for {
          di :: dj :: Nil <- ds.iterator
          (yi, yj) = (i + di, j + dj)
          q = nc2(yi) + yj
          if yi >= 1 && 1 <= yj && yj <= yi
          if !(path contains q) && isPrime(q)
          xs <- search1(yi, yj, q :: path)
        } yield xs
    }

    def search2(i: Long, j: Long) =
      (ds count {
        case di :: dj :: Nil =>
          val q = nc2(i + di) + j + dj
          isPrime(q)
        case _ => false
      }) >= 2

    val ts = for {
      i <- is
      j <- 1L to i
      p = nc2(i) + j
      if isPrime(p)
      if search2(i, j) || search1(i, j, p :: Nil).hasNext
    } yield p
    ts.sum
  }

  def p197(N: Long = 1000000000000L) = {
    val M = 1000
    def f(x: Long) = {
      val xd = x / 1e9
      floor(pow(2, 30.403243784 - xd * xd)).toLong
    }

    def us = (Iterator iterate -1000000000L)(f)
    val x = (us sliding 2 map (_.sum) drop M).next
    "%.9f" format (x / 1e9)
  }

  def p198(N: Long = 10 ** 8, M: Long = 100) = {
    import Utils.Rational

    def f(xs: List[Long]): Long = {
      val hd :: tl = xs
      val sums = new Iterator[Long] {
        var i = hd
        def ys = i :: tl
        def hasNext = {
          val (p, q) = cfEval((0L :: ys.reverse ::: ys.tail).iterator).last
          q <= N
        }

        def next = {
          val s = (if (i % 2 == 0) 1 else 0) + f(1 :: ys)
          i += 1
          s
        }
      }
      sums.sum
    }

    f(List(M)) - 1 // exclude 1/100
  }

  def p199(N: Int = 10) = {
    import syntax.traverse._
    import std.list._

    case class Circle(p: Complex[Double], r: Double) {
      def k = 1.0 / r
    }

    val cs0 = mutable.Buffer[Circle]()
    val ts0 = mutable.Set[(Circle, Circle, Circle)]()

    cs0 += Circle(Complex(0, 0), -1)
    0 until 3 foreach { i =>
      cs0 += Circle(Complex.polar(4 - 6 / sqrt(3), i * pi / 3), 2 * sqrt(3) - 3)
    }

    ts0 += ((cs0(0), cs0(1), cs0(2)))
    ts0 += ((cs0(0), cs0(2), cs0(3)))
    ts0 += ((cs0(0), cs0(3), cs0(1)))
    ts0 += ((cs0(1), cs0(2), cs0(3)))

    // http://en.wikipedia.org/wiki/Descartes'_theorem
    def iter(ts: Set[(Circle, Circle, Circle)]) = {
      val cs = mutable.Buffer[Circle]()
      val rs = mutable.Set[(Circle, Circle, Circle)]()

      for ((a, b, c) <- ts) {
        val det = a.k * b.k + b.k * c.k + c.k * a.k
        val dk = a.k + b.k + c.k + 2 * sqrt(a.k * b.k + b.k * c.k + c.k * a.k)
        val dp = (a.k * a.p + b.k * b.p + c.k * c.p
          + 2 * sqrt(a.k * b.k * a.p * b.p + b.k * c.k * b.p * c.p + c.k * a.k + c.p * a.p)) / dk
        val d = Circle(dp, 1.0 / dk)
        cs += d
        rs += ((d, a, b))
        rs += ((d, b, c))
        rs += ((d, c, a))
      }

      (rs, cs)
    }

    val (_, css) = ((0 until N).toList traverseS (_ => State(iter))).apply(ts0)
    val cs = (cs0 drop 1) ++ css.flatten
    val r = 1.0 - (cs map (_.r ** 2)).sum / (cs0.head.r ** 2)
    "%.8f" format r
  }

  def p200(N: Int = 200) = {
    val m0 = 10 ** 6
    val ps = (primes(m0) map (_.toBigInt)).toList

    def isPrimeProof(zs: List[Int]) = {
      val ps = for {
        k <- (0 until zs.length).iterator
        j <- 0 until 10
        ys = zs.zipWithIndex map { case (z, i) => if (i == k) j else z }
        if ys.head != 0 && zs(k) != j
        if millerRabin(joinBase[BigInt](10, ys))
      } yield ys
      !ps.hasNext
    }

    tunel() { m1: Long =>
      val xs = (for {
        p <- ps.par
        q <- ps takeWhile (q => p * p * q * q * q <= m1)
        if (p != q)
        x = p * p * q * q * q
        zs = split10(x)
        if zs containsSlice List(2, 0, 0)
        if isPrimeProof(zs)
      } yield x).to[SortedSet]
      (xs drop (N - 1)).headOption
    }
  }

  def p201(N: Int = 100) = {
    val M = N / 2
    def xs(i: Int) = (i + 1) ** 2

    val Q = (Vector(Map(0 -> 1)) /: (0 until N)) {
      (P, i) =>
        val x = xs(i)
        val Q = Vector.fill(i + 2)(mutable.HashMap[Int, Int]() withDefaultValue 0)
        for {
          (zP, j) <- P.zipWithIndex
          (s, c) <- zP
        } {
          if (j + 1 <= M)
            Q(j + 1)(s + x) += c
          if (M - j <= N - i)
            Q(j)(s) += c
        }
        Q
    }

    (Q(M) filter { _._2 == 1 } map (_._1)).sum
  }

  def p202(N: Long = 12017639147L) = {
    val x = (N + 3) / 2
    val ys = (divide(-x - 1, 3) + 1)._2 to (x - 1) by 3
    ys count { y => gcd(y, x - y) == 1 }
  }

  def p203(N: Int = 51) = {
    val ts = for {
      i <- 0 until N
      j <- 0 to i
      p = ncr(i, j)
      if factor2(p) forall (_._2 == 1)
    } yield p
    ts.toSet.sum
  }

  def p204(N: Long = 10 ** 9, M: Int = 100) = {
    val ps = primes(M + 1).toIndexedSeq

    def f(i: Int, x: Long): Int =
      if (x > N)
        0
      else
        1 + f(i, x * ps(i)) + (i + 1 until ps.length map { j => f(j, ps(j) * x) }).sum

    f(0, 1L)
  }

  def p205() = {
    val as = genExp(convolve)(0 +: (mutable.Buffer fill 4)(1), 9)
    val ad = 4 ** 9
    val bs = genExp(convolve)(0 +: (mutable.Buffer fill 6)(1), 6)
    val bd = 6 ** 6

    val bcum = sums(bs)
    val p = (as.zipWithIndex map {
      case (a, ai) =>
        val b = if (ai < bcum.length) bcum(ai) else bcum.last
        (1.0 * a / ad) * (1.0 * b / bd)
    }).sum
    "%.7f" format p
  }

  def p206() = {
    def isSquare(x: Long) = isqrt(x) ** 2 == x
    val ts = for {
      ds <- ndIndex((List fill 8)(10))
      xs = (1 to 8 zip ds flatMap { case (c, d) => List(c, d) }) :+ 9
      x = joinBase[Long](10, xs)
      if isSquare(x)
    } yield x
    10 * isqrt(ts.next)
  }

  def p207(p: Long = 1, q: Long = 12345) = {
    def isPow(s: Int) = 2 ** ilog(2, s) == s

    val ts = runningCount(Iterator from 2 map isPow)
    val ix = (ts.zipWithIndex find (z => q * z._1 < p * z._2)).get._2 + 1
    val s = (ix + 2 - 1).toLong
    s * (s - 1)
  }

  def p208(N: Int = 70) = {
    val M = 5
    type Key = (List[Int], Int)

    val f = memoizeY(
      (key: Key, f: Key => Long) => {
        val (xs, t) = key
        if ((xs forall (_ == 0)) && t == 0)
          1L
        else {
          val cs = for {
            d <- List(-1, 1)
            r = divide(t + d, M)._2
            x = xs(r)
            if x > 0
          } yield f(xs updated (r, x - 1), r)
          cs.sum
        }
      })

    f((List fill M)(N / M), 0)
  }

  def p209() = {
    def f(xs: List[Int]) =
      (xs drop 1) :+ (xs(0) ^ xs(1) & xs(2))

    val M = (for {
      xs <- ndIndex((List fill 6)(2))
      ys = f(xs)
      x = joinBase[Int](2, xs)
      y = joinBase[Int](2, ys)
    } yield (x, y)).toMap

    val P = mutable.Map[Int, Int]() withDefault identity
    def union(i: Int, j: Int) =
      P(find(i)) = find(j)

    def find(i: Int): Int = {
      val j = P(i)
      if (i != j)
        find(j)
      else
        i
    }

    M foreach { case (i, j) => union(i, j) }

    val G = M.keys groupBy find
    (G.values map (_.size) map (z => fibonacci(z + 2) - fibonacci(z - 2))).qproduct
  }

  def p210(N: Long = 10 ** 9) = {
    val t = N / 8
    (for {
      x <- (0L to isqrt(2 * t * t)).iterator
      det = 2 * t * t - x * x
      s = (if (x != 0) 2 else 1) * (2 * isqrt(det - 1) + 1)
    } yield s).sum - (N / 4 - 1) + 3 * N * N / 2
  }

  def p211(N: Long = 64000000L) = {
    val ts = ((1L until N).par
      filter { x =>
        val fs = factor2(x)
        val s = sigma(fs map { case (p, a) => (p.toBigInt, a) }, 2)
        isSquare(s)
      })
    ts.sum
  }

  def p212(N: Int = 50000) = {
    val k0 = 10000
    val k1 = 400

    case class Box(p: List[Int], w: List[Int], sign: Int = 1) {
      def intersect(b: Box) = {
        val cp = (0 until 3).toList map { k => max(p(k), b.p(k)) }
        val cq = (0 until 3).toList map { k => min(p(k) + w(k), b.p(k) + b.w(k)) }
        val cw = cp zip cq map { case (p, q) => q - p }

        if (cw forall (_ > 0)) {
          val c = Box(cp, cw, -1 * sign * b.sign)
          Some(c)
        } else
          None
      }
    }

    val M = mutable.Map.empty[(Int, Int), mutable.Buffer[Box]] withDefaultValue mutable.Buffer.empty[Box]

    def addBox(b: Box) = {
      val (u, v) = (b.p(0) / k1, b.p(1) / k1)
      M getOrElseUpdate ((u, v), mutable.Buffer.empty[Box]) += b
    }

    def evalBox(b: Box) = {
      val (u, v) = (b.p(0) / k1, b.p(1) / k1)
      val as = for {
        du <- -1 to 1
        dv <- -1 to 1
        a <- M(u + du, v + dv)
      } yield a

      as foreach { a =>
        a intersect b match {
          case Some(c) => addBox(c)
          case None => ()
        }
      }

      addBox(b)
    }

    def volume = (for {
      as <- M.values
      a <- as
    } yield a.sign * a.w.product.toBigInt).qsum

    val lfg = lfgIterator
    val boxes = Iterator continually {
      val p = (List fill 3)(lfg.next % k0)
      val w = (List fill 3)(1 + lfg.next % (k1 - 1))
      Box(p, w)
    } take N

    boxes foreach evalBox
    volume
  }

  def p213(N: Int = 50, M: Int = 30) = {
    val M2 = M ** 2

    val D0 = {
      val D = (mutable.Buffer fill (M2, M2))(0.0)
      for {
        ix <- 0 until M2
      } D(ix)(ix) = 1.0
      D
    }

    def iter(D0: mutable.Buffer[mutable.Buffer[Double]]) = {
      val D1 = (mutable.Buffer fill (M2, M2))(0.0)

      for {
        ai <- 0 until M
        aj <- 0 until M
        d0a = D0(M * ai + aj)
        d1a = D1(M * ai + aj)
        bi <- 0 until M
        bj <- 0 until M
        ts = {
          var ts = List.empty[Int]
          if (bi > 0)
            ts ::= M * (bi - 1) + bj
          if (bi < M - 1)
            ts ::= M * (bi + 1) + bj
          if (bj > 0)
            ts ::= M * bi + bj - 1
          if (bj < M - 1)
            ts ::= M * bi + bj + 1
          ts
        }
        t <- ts
      } d1a(t) += d0a(M * bi + bj) / ts.length

      D1
    }

    val D = ((Iterator iterate D0)(iter) drop N).next
    val es = 0 until M2 map {
      jx => (0 until M2 map { ix => 1.0 - D(ix)(jx) }).product
    }
    "%.6f" format es.sum
  }

  def p214(N: Int = 40000000, M: Int = 25) = {
    val ps = primes(N).to[SortedSet]

    val f = memoizeY(
      (x: Int, f: Int => Int) =>
        if (x == 1)
          1
        else if (ps contains x)
          f(x - 1) + 1
        else
          f(phi(x)) + 1)

    (ps filter (f(_) == M) map (_.toLong)).sum
  }

  def p215() = {

  }

  // 806s really slow
  def p216(N: Long = 50000000L) =
    (2L to N).par map (x => 2 * (x.toBigInt ** 2) - 1) count millerRabin

  def p217(N: Int = 47) = {
    val M = 3L ** 15

    val f = memoizeY(
      (jd: (Int, Int), f: ((Int, Int)) => (Long, Long)) => {
        val (j, d) = jd

        if (9 * (j / 2) < abs(d))
          (0L, 0L)
        else if (j <= 0)
          (1L, 0L)
        else if (j == 1)
          (10L, 45L)
        else {
          val ts = for {
            a <- 0 to 9
            b <- 0 to 9
          } yield {
            val (c, s) = f(j - 2, d + a - b)
            (c, 10 * s + c * b + c * a * powmod(10L, j - 1, M))
          }
          ((ts map (_._1)).sum % M, (ts map (_._2)).sum % M)
        }
      })

    def g(j: Int) = {
      val s = f(j, 0)._2 - (for {
        b <- 0 to 9
        (c, s) = f(j - 2, -b)
      } yield 10 * s + c * b).sum
      divide(s, M)._2
    }
    (1 to N map g).sum % M
  }

  def p218(N: Long = 10L ** 16) = {
    def f(n: Long) = (for {
      m <- Iterator from (n.toInt + 1) map (_.toLong)
      if (m - n) % 2 == 1 && gcd(m, n) == 1
      (_u, _v, _) = pythagoreanTriple(m, n, 1L)
      List(u, v) = List(_u, _v) sortBy (-_)
    } yield pythagoreanTriple(u, v, 1L)) takeWhile (_._3 <= N)

    val abcs = for {
      abcs <- Iterator from 1 map (f(_).toBuffer) takeWhile (!_.isEmpty)
      abc <- abcs
    } yield abc

    abcs count {
      case (a, b, _) =>
        val area = a.toBigInt * b / 2
        !(area % 6 == 0 && area % 28 == 0)
    }
  }
}





