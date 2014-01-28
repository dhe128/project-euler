package euler.dhe32.com

object Implicits {
  implicit class IteratorExtensions[A](xs: Iterator[A]) {
    def takeTo(p: A => Boolean): Iterator[A] = {
      val (before, after) = xs span p
      before ++ (after take 1)
    }

    def dropTo(p: A => Boolean): Iterator[A] = (xs dropWhile p) drop 1

    def last: A = {
      var a: A = xs.next
      xs foreach (x => a = x)
      a
    }
  }

  implicit class TraversableOnceExtensions[A](xs: TraversableOnce[A]) {
    import scala.concurrent._
    import scala.concurrent.duration._
    import java.util.concurrent.LinkedBlockingQueue

    def parMap[B](f: A => B)(implicit ctx: ExecutionContext): Iterator[B] = {
      val threads = Runtime.getRuntime.availableProcessors
      val q = new LinkedBlockingQueue[Option[Future[B]]](threads)

      future {
        xs foreach { x =>
          q put Some(future { f(x) })
        }
        q put None
      }

      new Iterator[B] {
        var topt: Option[Future[B]] = null
        def hasNext = take != None
        def next = {
          val t = take.get
          topt = null
          Await.result(t, Duration.Inf)
        }
        def take = {
          if (topt == null)
            topt = q.take
          topt
        }
      }
    }

    def parFilter(pred: A => Boolean)(implicit ctx: ExecutionContext): Iterator[A] =
      xs parMap (x => (x, pred(x))) filter (_._2) map (_._1)

    /*
    def parMapWithoutOrder[B](f: A => B)(implicit ctx: ExecutionContext): Iterator[B] = {
      val threads = Runtime.getRuntime.availableProcessors
      val q1 = new LinkedBlockingQueue[Boolean](threads)
      val q2 = new LinkedBlockingQueue[B](threads)

      future {
        xs foreach { x =>
          q1 put true
          future {
            val y = f(x)
            q2 put y
          }
        }
        q1 put false
      }

      new Iterator[B] {
        def hasNext = q1.isEmpty || q1.peek
        def next = {
          val y = q2.take
          q1.take
          y
        }
      }
    }
    * 
    */
  }
}