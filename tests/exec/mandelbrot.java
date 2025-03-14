
class Mandelbrot {

    int steps;

    Mandelbrot(int steps) {
        this.steps = steps;
    }

    /* arithmetique de virgule fixe
       precision q = 8192 i.e. 13 bits pour la partie decimale */

    int add(int x, int y) {
        return x + y;
    }
    int sub(int x, int y) {
        return x - y;
    }
    int mul(int x, int y) {
        int t = x * y;
        return (t + 8192 / 2) / 8192;
    }
    int div(int x, int y) {
        int t = x * 8192;
        return (t + y / 2) / y;
    }
    int of_int(int x) {
        return x * 8192;
    }

    boolean iter(int n, int a, int b, int xn, int yn) {
        if (n == 100) return true;
        int xn2 = mul(xn, xn);
        int yn2 = mul(yn, yn);
        if (add(xn2, yn2) > of_int(4)) return false;
        return iter(n+1, a, b, add(sub(xn2, yn2), a),
                    add(mul(of_int(2), mul(xn, yn)), b));
    }

    boolean inside(int x, int y) {
        return iter(0, x, y, of_int(0), of_int(0));
    }

    void run() {
        int xmin = of_int(-2);
        int xmax = of_int(1);
        int deltax = div(sub(xmax, xmin), of_int(2 * steps));
        int ymin = of_int(-1);
        int ymax = of_int(1);
        int deltay = div(sub(ymax, ymin), of_int(steps));
        int i;
        for (i = 0; i < steps; i=i+1) {
            int y = add(ymin, mul(of_int(i), deltay));
            int j;
            for (j = 0; j < 2 * steps; j=j+1) {
                int x = add(xmin, mul(of_int(j), deltax));
                if (inside(x, y))
                    System.out.print("0");
                else
                    System.out.print("1");
            }
            System.out.print("\n");
        }

    }

}

class Main {
    public static void main(String args[]) {
        new Mandelbrot(30).run();
    }
}
