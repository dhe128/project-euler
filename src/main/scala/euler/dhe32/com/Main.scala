package euler.dhe32.com

object Main {
  def main(args: Array[String]) = {
    val timer = Timer()
    val sol = Problems.p218()
    val end = System.currentTimeMillis()

    println(sol)
    println("")
    println(timer)
  }
}

case class Timer() {
  var start = System.currentTimeMillis()

  def get = {
    val end = System.currentTimeMillis()
    (end - start) / 1000.0
  }

  override def toString = ("%.3f" format get) + "s"
}