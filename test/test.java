class A {
  int a;
  A b;
  A(int n) {
    if (n == 0) return;
    else
    System.out.print("n > 0 \n");
    a = n; b = new A(n-1);}
}
class Main {
  public static void main(String args[]) {
    A a = new A(3);
    if (a.a == 3 && a.b.a == 2 && a.b.b.a == 1 && a.b.b.b.a == 0)
      System.out.print("Test passed \n");
    else
      System.out.print("Test failed  \n");
  }
}
