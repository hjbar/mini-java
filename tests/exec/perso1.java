class A {

    A() {}

    int f() {
	System.out.print("Hello world !\n");
	return 42;
    }

}

class B extends A {

    int a;
    int b;

    B(int n, int d) {
	a = n;
	b = d;
    }

}

class Main {

    public static void main(String args[]) {

	A a = new A();
	new B(42, a.f());
	System.out.print("ok\n");

    }

}
