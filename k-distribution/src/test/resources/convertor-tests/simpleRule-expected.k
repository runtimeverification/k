// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module TEST [location(startLine(3),startColumn(1),endLine(6),endColumn(9))]
  syntax Exp [location(startLine(4),startColumn(3),endLine(4),endColumn(12))]
  rule A [location(startLine(5),startColumn(8),endLine(5),endColumn(13)) sort(Exp)]=>A [location(startLine(5),startColumn(17),endLine(5),endColumn(18)) sort(Exp)] requires true ensures true [location(startLine(5),startColumn(3),endLine(5),endColumn(17))]
endmodule
