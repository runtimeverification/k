#include "cdd.h"

//#define D 5.0
//#define T 300.0
#define SP_MAX 600.0
//#define VE_MAX 1200.0
//#define DS_MAX 100.0

//#define E_sqv 0x1.p-30
//#define E_sqs 0x1.p-37
//#define E_dot 0x1.p-34
//#define E_hlos 0x1.p-36
//#define E_tau 0x1.p-21
#define E_omega 0x1.p-1
#define E_cd2d 0x2.p-1
#define SPEED(v) (-SP_MAX <= (v) <= SP_MAX)
//#define VELOCITY(v) (-VE_MAX <= (v) <= VE_MAX)
//#define DISTANCE(x) (-DS_MAX <= (x) <= DS_MAX)

#define TRUE(p) ((p)!=0)
#define FALSE(p) ((p)==0)

/*@ ensures \result == dmax(a,b); */
double max(double a, double b){
    return (a<=b)?b:a;
}
/*@ ensures \result == dmin(a,b); */
double min(double a, double b){
    return (a<=b)?a:b;
}
/*@
  requires VELOCITY(x) && VELOCITY(y) ;
  ensures \abs(\result - sqR(x,y)) < E_sqv ;
  assigns \nothing ;
  @*/
double sqv(double x,double y) { return x*x + y*y; }

/*@
  requires DISTANCE(x) && DISTANCE(y) ;
  ensures \abs(\result - sqR(x,y)) < E_sqs ;
  assigns \nothing ;
  @*/
double sqs(double x,double y) { return x*x + y*y; }

/*@
  requires DISTANCE(u_x) && DISTANCE(u_y);
  requires VELOCITY(v_x) && VELOCITY(v_y);
  ensures \abs(\result - dotR(u_x, u_y, v_x, v_y)) < E_dot ;
  assigns \nothing ;
  @*/
double dot(double u_x, double u_y, double v_x, double v_y){
  return u_x * v_x + u_y * v_y ;
}

/*@
  requires DISTANCE(s_x) && DISTANCE(s_y);
  ensures horizontal_losR(s_x,s_y,D) ==> TRUE(\result);
  assigns \nothing ;
  @*/
int horizontal_los(double s_x, double s_y)
{
  double sqS = sqs(s_x, s_y);
  double sqD = D*D;
  return (sqS - sqD <= E_hlos);
}

/*@  requires DISTANCE(s_x) && DISTANCE(s_y);
     requires VELOCITY(v_x) && VELOCITY(v_y);
      ensures  \abs(\result - tauR(s_x, s_y, v_x, v_y,0.0,T)) <= E_tau ;
  @*/
double tau_vv(double s_x, double s_y, double v_x, double v_y){
  return min(max(0.0, - dot(s_x,s_y, v_x, v_y)), 300.0*sqv(v_x, v_y));
}

/*@  requires DISTANCE(s_x) && DISTANCE(s_y);
     requires VELOCITY(v_x) && VELOCITY(v_y);
     ensures \abs(\result - omega_vvR_outDr(s_x,s_y,v_x,v_y,D,0.0,T)) < E_omega;
 */

double omega_vv(double s_x, double s_y, double v_x, double v_y){
    double tau;

    /* if (ond(s_x, s_y, D*D) && (Br==0)) { */
    /*     return dot(s_x, s_y, v_x, v_y); */
    /* } */
    /* else { */
    
    tau = tau_vv(s_x, s_y, v_x, v_y);
    return sqv(v_x, v_y)*sqv(s_x, s_y) + (2 * tau)* dot(s_x, s_y, v_x, v_y) + tau*tau - D*D*sqv(v_x,v_y);
  
}

/*@   requires DISTANCE(s_x) && DISTANCE(s_y);
      requires VELOCITY(v_x) && VELOCITY(v_y);
      requires !on_Dr(s_x,s_y, D);
      requires cd2d(s_x,s_y,v_x,v_y,D,0.0,T); 
      ensures TRUE(\result); 
*/

int cd2d(double s_x, double s_y, double v_x, double v_y){
  /*@  assert horizontal_losR(s_x,s_y,D) || omega_vvR_outDr(s_x,s_y,v_x,v_y,D,0.0,T) < 0 ; */ 
  return  (horizontal_los(s_x, s_y)) ||  (omega_vv(s_x, s_y, v_x, v_y) <= E_cd2d);
   
}
