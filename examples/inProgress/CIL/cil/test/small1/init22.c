//Test for a compound initializer bug.   The if statement for t?2:3 was being
//added twice.

//Bug report from Peter Hawkins, based on 
//linux-2.6.17.1/net/ipv4/route.c:ip_route_output_slow

//Patch by Benjamin Monate

struct bar {
     int x;
};
struct foo {
     struct bar b;
     int y;
};

int rand(void);

int main() {
     int t = rand();
     struct foo f = {
         .b = {
             .x = (t?2:3),
         },
         .y = 42
     };
     return 0;
}
