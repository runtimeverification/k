#include "helpers.h"

int main(int argc, char **Argv) {
        unsigned i;
	float X = 1.234;
	float Y = 9.876;
        float Z = 1.111;
        double U = 873.1834;
        double V = 1842.9028;
	FV Af, Bf, Cf, Df;
	DV Ad, Bd;
	if (argc == 1123) X = 2.38213;
        if (argc == 1432) Y = 7.71945;
        if (argc == 2123) U = 32.8219;
        if (argc == 5123) V = 77.7998;

        for (i = 0; i < 500000; ++i) {
          Af.V = (v4sf){ X, X, X, X };  // splat
          Af.V = Af.V * Af.V;
          
          Bf.V = (v4sf){ X, X, 0, 0 };
          Bf.V = Bf.V+Bf.V;
          
          Cf.V = (v4sf){ X, X, Y, Y };
          Cf.V = Cf.V+Cf.V;

          Df.V = (v4sf){ Y, Y, Z, Z };
          Df.V = Df.V+Df.V;

          Ad.V = (v2sd){ U, U }; // splat
          Ad.V = Ad.V+Ad.V;

          Bd.V = (v2sd){ U, V };
          Bd.V = Bd.V+Bd.V;
        }
        
        printFV(&Af);
        printFV(&Bf);
        printFV(&Cf);
        printFV(&Df);
        printDV(&Ad);
        printDV(&Bd);
        return 0;
}

