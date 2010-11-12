/*@ requires  y/2 <= x <= 2*y  && \round_error(x)==0 && \round_error(y)==0
  @ ensures  \round_error(\result)==0
  @*/

double Sterbenz(double x, double y) {
  return x-y;
}

