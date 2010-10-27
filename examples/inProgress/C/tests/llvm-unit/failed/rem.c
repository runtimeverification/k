#include <stdio.h>
#include <stdlib.h>

// Simple REM test case. Tests some basic properties of remainder
// operation. 

// All macros must evaluate to true. x,y can be signed/unsigned, m
// should be unsigned.

// Returns true if multiplication will overflow.
#define MultOverflow(x,y) ((((x) * (y)) / (y)) != (x))

// x == y => (x mod m) == (y mod m)
#define CongruenceTest(x,y,m) \
    (((x) != (y)) || (((x) % (m)) == ((y) % (m))))


/******************************************************************
 * These three tests can be done only for unsigned case because they
 * contain add/sub. If you're eager to get this working with signed
 * numbers, take care of overflows.
 ******************************************************************/

// Return true if add/sub will cause overflow.
#define UnsignedAddOverflow(x,y) (((x) + (y)) < (x))
#define UnsignedSubUnderflow(x,y) (((x) - (y)) > (x))

// ((x % m) + (y % m)) % m = (x + y) % m
#define AdditionOfCongruences(x,y,m) \
    (UnsignedAddOverflow((x)%(m),(y)%(m)) || \
    UnsignedAddOverflow((x),(y)) || \
    (((((x) % (m)) + ((y) % (m))) % m) == (((x) + (y)) % (m))))

// ((x % m) == ((y + z) % m)) == (((x - z) % m) == (y % m))
#define SimpleCongruenceEquation(x,y,z,m) \
    (UnsignedAddOverflow((y),(z)) || \
     UnsignedSubUnderflow((x),(z)) || \
    ((((x) % (m)) == (((y) + (z)) % (m))) % m) == \
    ((((x) - (z)) % (m)) == ((y) % (m))))

// If y*m does not overflow: (x % m) == (x + y*m) % m
#define AdditionOfMultipleOfModIsNOP(x,y,m) \
    (MultOverflow(y,m) || \
     UnsignedAddOverflow((x),(y)*(m)) || \
    (((x) % (m)) == (((x) + ((y)*(m))) % (m))))

/******************************************************************/
    
// Greatest common divisor
long gcd(long a, long b) {
    long c;
    while(1) {
        c = a % b;
        if(c == 0) return b;
        a = b;
        b = c;
    }
}

// If gcd(z,m)==1: ((x == y) % m) == ((x / z == y / z) % m). This holds
// only if both sides are actually divisble by z.
#define BothSidesCanBeDividedWithDivisorMutuallyPrimeWithMod(x,y,z,m) \
    ((gcd((z),(m)) != 1) || ((z) == 0) || \
    (gcd((x),(z)) != (z)) || ((gcd((y),(z)) != (z))) || \
    (((x) % (m)) == ((y) % (m))) == (((((x) / (z)) % m) == (((y) / (z))) % m)))

// If z divides x,y,m: ((x % m) == (y % m)) == (((x/z) % (m/z)) == ((y/z) % (m/z)))
#define DivideBothSidesAndModulus(x,y,z,m) \
    (((z) == 0) || (gcd((x),(z)) != (z)) || \
    (gcd((y),(z)) != (z)) || \
    (gcd((m),(z)) != (z)) || \
    (((x)%(m)) == ((y)%(m))) == \
    ((((x)/(z)) % ((m)/(z))) == (((y)/(z)) % ((m)/(z)))))

// If z divides m, than: ((x % m) == (y % m)) == ((x % z) == (y % z))
// z should be unsigned.
#define SubModulusTest(x,y,z,m) \
    (((z) == 0) || (gcd((m),(z)) != (z)) || \
    ((((x)%(m)) == ((y)%(m))) == (((x)%(z)) == ((y)%(z)))))

// Runs the test c under number t.
#define test(t,c) \
if (!c) { \
printf("Test #%u, failed in iteration #: %u\n", t, idx); \
printf("Failing test vector:\n"); \
printf("m=%u, x_u=%u, y_u=%u, z_u=%u, x_s=%d, y_s=%d, z_s=%d\n", \
    m, x_u, y_u, z_u, x_s, y_s, z_s); \
return 1; \
}

// The higher the number the better the testing. 
#define ITERATIONS 100

int main(int argc, char **argv) {
    // Since the test vectors are printed out anyways, I suggest leaving
    // the test nondeterministic. Many people run tests on various
    // machines, so REM-related code will be covered with a much better
    // coverage... If you really don't like the idea of having better
    // coverage, uncomment the following line:

    //srand(0xA392049F);

    unsigned idx = 0;
    for (; idx < ITERATIONS; ++idx) {
        unsigned m = (unsigned)rand();

        if (m == 0) { // Repeat again
            idx--; continue;
        }

        unsigned x_u = (unsigned)rand();
        unsigned y_u = (unsigned)rand();
        unsigned z_u = (unsigned)rand();
        
        int x_s = (rand() % 2) ? rand() : -rand();
        int y_s = (rand() % 2) ? rand() : -rand();
        int z_s = (rand() % 2) ? rand() : -rand();

        test(1, CongruenceTest(x_s, y_s, m));
        test(2, CongruenceTest(x_s, y_u, m));
        test(3, CongruenceTest(x_u, y_s, m));
        test(4, CongruenceTest(x_u, y_u, m));
        
        test(5, AdditionOfCongruences(x_u, y_u, m));

        test(6, SimpleCongruenceEquation(x_u, y_u, z_u, m));
        
        test(7, AdditionOfMultipleOfModIsNOP(x_u, y_u, m));

        test(8, BothSidesCanBeDividedWithDivisorMutuallyPrimeWithMod(x_s, y_s, z_s, m));
        test(9, BothSidesCanBeDividedWithDivisorMutuallyPrimeWithMod(x_s, y_s, z_u, m));
        test(10, BothSidesCanBeDividedWithDivisorMutuallyPrimeWithMod(x_s, y_u, z_s, m));
        test(11, BothSidesCanBeDividedWithDivisorMutuallyPrimeWithMod(x_s, y_u, z_u, m));
        test(12, BothSidesCanBeDividedWithDivisorMutuallyPrimeWithMod(x_u, y_s, z_s, m));
        test(13, BothSidesCanBeDividedWithDivisorMutuallyPrimeWithMod(x_u, y_s, z_u, m));
        test(14, BothSidesCanBeDividedWithDivisorMutuallyPrimeWithMod(x_u, y_u, z_s, m));
        test(15, BothSidesCanBeDividedWithDivisorMutuallyPrimeWithMod(x_u, y_u, z_u, m));

        test(16, DivideBothSidesAndModulus(x_s, y_s, z_s, m));
        test(17, DivideBothSidesAndModulus(x_s, y_s, z_u, m));
        test(18, DivideBothSidesAndModulus(x_s, y_u, z_s, m));
        test(19, DivideBothSidesAndModulus(x_s, y_u, z_u, m));
        test(20, DivideBothSidesAndModulus(x_u, y_s, z_s, m));
        test(21, DivideBothSidesAndModulus(x_u, y_s, z_u, m));
        test(22, DivideBothSidesAndModulus(x_u, y_u, z_s, m));
        test(23, DivideBothSidesAndModulus(x_u, y_u, z_u, m));

        test(25, SubModulusTest(x_s, y_s, z_u, m));
        test(27, SubModulusTest(x_s, y_u, z_u, m));
        test(29, SubModulusTest(x_u, y_s, z_u, m));
        test(31, SubModulusTest(x_u, y_u, z_u, m));
    }
    printf("\n *** REM test done! ***\n");
    return 0;
}
