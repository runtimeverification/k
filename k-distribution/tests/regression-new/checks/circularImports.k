// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module A imports B endmodule
module B imports C endmodule
module C imports D endmodule
module D imports E endmodule
module E imports A endmodule
