package euler.dhe32.com;

import java.util.*;

public class JavaProblems {
  public static void main(String[] args) {
    System.out.println(p201());
  }

  public static long p201() {
    return new p201(100).solve();
  }

  public static class p201 {
    int m;
    int n;

    public p201(int n) {
      this.n = n;
      this.m = n / 2;
    }

    public int[] xs2 = new int[] { 1, 3, 6, 8, 10, 11 };

    public int xs(int i) {
      return (i + 1) * (i + 1);
    }

    public long solve() {
      Vector<HashMap<Integer, Integer>> P = new Vector<HashMap<Integer, Integer>>();
      P.add(new HashMap<Integer, Integer>());
      P.get(0).put(0, 1);

      for (int i = 0; i < n; i++) {
        Vector<HashMap<Integer, Integer>> Q = new Vector<HashMap<Integer, Integer>>();
        for (int j = 0; j < P.size() + 1; j++)
          Q.add(new HashMap<Integer, Integer>());

        for (int j = 0; j < P.size(); j++)
          for (Map.Entry<Integer, Integer> kv : P.get(j).entrySet()) {
            int x = kv.getKey();
            int c = kv.getValue();
            int x2 = x + xs(i);
            if (j + 1 <= m) {
              Integer z = Q.get(j + 1).get(x2);
              Q.get(j + 1).put(x2, (z != null ? z : 0) + c);
            }
            if (m - j <= n - i) {
              Integer z = Q.get(j).get(x);
              Q.get(j).put(x, (z != null ? z : 0) + c);
            }
          }

        P = Q;
      }

      Vector<Integer> cs = new Vector<Integer>();
      for (Map.Entry<Integer, Integer> kv : P.get(m).entrySet()) {
        if (kv.getValue() == 1)
          cs.add(kv.getKey());
      }

      long sum = 0L;
      for (int c : cs)
        sum += c;

      return sum;
    }
  }
}
