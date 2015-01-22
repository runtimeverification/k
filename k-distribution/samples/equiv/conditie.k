// Copyright (c) 2013-2015 K Team. All Rights Reserved.
krun sum1.minimp -cPGM2 "`cat prove2.minfun`" -cPC "symInt(s) ==Int (symInt(i) *Int (symInt(i) -Int 1)) /Int 2" --parser "kast -groundParser" --compiled-def ./runechiv-kompiled/
