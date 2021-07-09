%Parameters
int: f;
int: g;
int: c;
int: k;
set of int: Cap = 0..k;
int: t;
set of int: Trips = 1..t;
int: pf;
int: pg;
int: pc;
set of int: maximum=0..max([f,g,c]);
%Variables
array[Trips] of var Cap:fox;
array[Trips] of var Cap:geese;
array[Trips] of var Cap:corn;
var Trips:trips;
var int:obj;
array[0..t] of var int:right_side_value;%Right side value in given time
array[0..t,1..2,1..3] of var maximum:side_fgc;%[time,side,type]Number of animals/corn that is on the given side in given time (trip)
%Predicates
predicate arrived(Trips:trip,1..2:side)=
  let{
  var 0..1:f_deaths,
  var 0..g:g_deaths,
  var 0..c:c_deaths
  }in
  cycle(trip,side,f_deaths,g_deaths,c_deaths)/\
  side_fgc[trip,side,1]=side_fgc[trip-1,side,1]+fox[trip]-f_deaths/\%We place everything on land and delete what died
  side_fgc[trip,side,2]=side_fgc[trip-1,side,2]+geese[trip]-g_deaths/\
  side_fgc[trip,side,3]=side_fgc[trip-1,side,3]+corn[trip]-c_deaths;

predicate departed(Trips:trip,1..2:side)=
  side_fgc[trip,side,1]=side_fgc[trip-1,side,1]-fox[trip]/\
  side_fgc[trip,side,2]=side_fgc[trip-1,side,2]-geese[trip]/\
  side_fgc[trip,side,3]=side_fgc[trip-1,side,3]-corn[trip];
  
predicate cycle(Trips:trip,1..2:side,var 0..1:f_deaths,var 0..g:g_deaths,var 0..c:c_deaths)=
  let{
  var 0..f:tmpfox=side_fgc[trip-1,side,1],
  var 0..g:tmpgeese=side_fgc[trip-1,side,2],
  var 0..c:tmpcorn=side_fgc[trip-1,side,3]
  }in
  if(tmpfox>0/\tmpcorn>0/\tmpgeese=0)then
    f_deaths=1/\c_deaths=1%Fox explode
  elseif(tmpfox>tmpgeese/\tmpgeese>0)then
    f_deaths=1%Fox bitten to death
  elseif(tmpgeese>=tmpfox/\tmpfox>0)then
    g_deaths=tmpfox%Geese were eaten
  elseif(tmpfox=0/\tmpgeese>tmpcorn/\tmpcorn>0)then
    g_deaths=1/\%Geese war
    c_deaths=1
  elseif(tmpfox=0/\tmpgeese<=tmpcorn/\tmpgeese>0)then
    c_deaths=tmpgeese%Geese ate corn
  else
    true
  endif;
%Constraints
constraint side_fgc[0,1,1]=f/\%Fox start
           side_fgc[0,2,1]=0/\
           side_fgc[0,1,2]=g/\%Geese start
           side_fgc[0,2,2]=0/\
           side_fgc[0,1,3]=c/\%Corn start
           side_fgc[0,2,3]=0;

constraint trips mod 2 == 1;%We always end on the right side
constraint forall(i in Trips where i mod 2 = 1)(departed(i,1)/\arrived(i,2));
constraint forall(i in Trips where i mod 2 = 0)(departed(i,2)/\arrived(i,1));
constraint forall(i in Trips)(fox[i]+geese[i]+corn[i]<=k);%We cant transport more than capacity
constraint forall(i in Trips where i mod 2 = 1 /\ i<=trips)(fox[i]+geese[i]+corn[i]>0);%If we travel left to right, we must have something loaded

constraint forall([not (geese[i] == geese[i-1] /\fox[i] == fox[i-1] /\ corn[i] == corn[i-1])| i in 2..trips where i mod 2 == 0]);%We dont want to travel back with the same things we just transported to right
constraint forall(i in 0..trips)(right_side_value[i]=side_fgc[i,2,1]*pf+side_fgc[i,2,2]*pg+side_fgc[i,2,3]*pc);%Right side must not decrease in value
constraint forall(i in 1..trips where i mod 2=1)(right_side_value[i-1]<right_side_value[i]);

constraint obj=right_side_value[trips];%Obj calculation

solve:: seq_search([
int_search([trips], input_order, indomain_max, complete),
int_search([ if p == 1 then fox[i] elseif p==2 then geese[i]  else corn[i] endif |i in 1..trips,p in 1..3 where i mod 2 =1], input_order, indomain_max, complete)
]) maximize obj;
output 
["fox    = ", show(fox), ";\n"] ++
["geese  = ", show(geese), ";\n"] ++
["corn   = ", show(corn), ";\n"] ++
["trips  = ", show(trips), ";\n"] ++
["obj    = ", show(obj), ";\n"]
