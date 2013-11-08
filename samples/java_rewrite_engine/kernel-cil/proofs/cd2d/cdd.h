
/*@
  axiomatic CD2D {
  logic real dmax(real x, real y) = (x<y) ? y : x;
  logic real dmin(real x, real y) = (x<y) ? x : y;

  logic real sqR (real x, real y) = x*x + y*y;
  logic real dotR (real ax, real ay, real bx, real by) = ax*bx + ay*by;
  logic real tauR(real ux, real uy, real v_x, real v_y, real b, real t) =
    dmin(dmax(b*sqR(v_x,v_y), - dotR(ux,uy, v_x, v_y)), t*sqR(v_x, v_y)) ;

   predicate horizontal_losR (real s_x, real s_y, real D) = sqR(s_x,s_y) < D*D; 

   predicate on_Dr (real s_x, real s_y, real D) = sqR(s_x, s_y) == D*D; 
   logic real omega_vvR (real s_x, real s_y, real v_x, real v_y, real D, real b, real t); 
 
 logic real omega_vvR_outDr (real s_x, real s_y, real v_x, real v_y, real D, real b, real t) =
       \let tau = tauR(s_x,s_y,v_x,v_y,b,t);
       (sqR(v_x,v_y) * sqR(s_x,s_y)
        + 2 * tau * dotR (s_x,s_y,v_x,v_y)
       + tau * tau       - D*D * sqR(v_x,v_y));

  axiom omega_vv_on_Dr:
    \forall real s_x,s_y,v_x,v_y,D,b,t ;
    on_Dr(s_x,s_y,D) ==>    omega_vvR(s_x,s_y,v_x,v_y,D,b,t) == dotR(s_x, s_y, v_x, v_y);

  axiom omega_vvR_outside_Dr:
    \forall real s_x,s_y,v_x,v_y,D,b,t ;
    !on_Dr(s_x,s_y,D) ==>
    omega_vvR(s_x,s_y,v_x,v_y,D,b,t) == omega_vvR_outDr(s_x,s_y,v_x,v_y,D,b,t);

// Specify the conflict detection algorithm

   predicate cd2d (real s_x, real s_y, real v_x, real v_y, real D, real B, real T) =
     horizontal_losR(s_x,s_y,D) || (omega_vvR(s_x,s_y,v_x,v_y,D,B,T) < 0);
  


  }
*/

