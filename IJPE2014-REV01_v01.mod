/*********************************************
 * OPL 12.4 Model
 * Author: gstecca
 * Creation Date: 01/dic/2012 at 18.17.43
 *********************************************/


 {int} N = ...; //{<1>, <3>, <4>, <5>}; // Graph nodes
// tuple shipment {
  // int k;
   //} // a shipment
   
  {int} K = ...; // shipments
  {int} Ksign = ...; // final product shipments
 //int R[L] = ...; // bom sublevels
 
 tuple bom {   // shipment (product) h is needed for product k
   int h;
   int k;
 }    
 
 {bom} Bom = ...;
 
 tuple endpoint {
   int i;
   int k;
 }
 {endpoint} Origins = ...;
 {endpoint} Destinations = ...;
 

 
 float alfa = ...; // credit value of 1 ton of co2
 
 tuple route {
   int i;
   int j;
   int k;   
 }
 {route} Routes = ...;
 
 {endpoint} I = {<i,k> | i in N, k in K, j in N : <i,j,k> in Routes || <j,i,k> in Routes} diff (Origins union Destinations);
 
 tuple arc {
   int i;
   int j;
 };
 {arc} Arcs =  ...;//{<i,j> | <i,j,k> in Routes};
 {int} NP = {i | i in N, <i,k> in Origins }; // nodes where producion is located
 
 //{nk} NK = {<i,k> | i in N, k in K, j in N : <i,j,k> in Routes}; // combinations of nodes-productions
 {endpoint} NK = I union Origins union Destinations;
 
 
 float p[Origins] = ...; // production cost
 int f[Origins] = ...; // activation cost for plants
 float FR[Routes] = ...; // activation cost for routes
 float T[Routes] = ...; // times tijk
 float wsu[K] = ...; // weight of shipment unit in tons (tons/units) of each shipment k wsu[K]
 float Cost[Arcs] = ...;
 float e[Arcs] = ...; // emissions
 int Q[Destinations] = ...; // quantity demanded
 float S[N] = ...; // service times
 float R[K] = ...; //Production times for shipments
 int lts[K] = ...; // Time of stock in hours(e.g 1 shift of stock = 8)
 float z1 = ...; // weight of transport cost
 float z2 = ...; // weight of production cost
 float z3 = ...; // weight of emission cost
 

 int Capacity[Arcs] = ...; //arc capacity
 int CapacityP[Origins] = ...; //Production nodes capacities
 
 int E = ...; // Early date
 int L = ...; // Due Date
 int M = ...; //big number
 //int ks = ...; // final shipment
 //int origin = ...; // final product origin
 //int destination = ...; // final product destination 
 //alfa = ...;
 //beta = ...; 
   
  
  dvar float+  X[Routes]; //verify if =0 is included
  dvar boolean  u[Routes];
  dvar boolean z[Origins];  
  dvar int w[NK];

  
  dexpr float Z_TransCost = sum(<i,j,k> in Routes) X[<i,j,k>] *wsu[k]* Cost[<i,j>] 
                           + sum(<i,j,k> in Routes) FR[<i,j,k>]* u[<i,j,k>];
  dexpr float z_ProdCost = sum (o in Origins, <o.i,j,o.k> in Routes)X[<o.i,j,o.k>]*p[o] + 
                sum (o in Origins)z[o]*f[o];
  dexpr float z_EmisFact =  alfa*sum (<i,j,k> in Routes)X[<i,j,k>]*wsu[k]*e[<i,j>];
                 
  dexpr float Z = z1*Z_TransCost + z2*z_ProdCost + z3*z_EmisFact;// + w[destination][ks] ;

  
  minimize Z;
  
  subject to {
    
    forall (k in Ksign)  //, <i,k> in Origins 
      ct_2:  
      sum(<i,j,k> in Routes : <i,k> in Origins) X[<i,j,k>] == sum(<nd,k> in Destinations)Q[<nd,k>];
      
      
    forall (k in Ksign, <j,k> in Destinations)
      ct_3:  
      sum(<i,j,k> in Routes) X[<i,j,k>] == Q[<j,k>];      
  
    forall (k in K diff Ksign)
      ct_4:  
      //sum(<i, k> in Origins, <i,j,k> in Routes) X[<i,j,k>] - sum(<j, k> in Destinations, <i,j,k> in Routes) X[<i,j,k>] ==0;
      sum(<i,j,k> in Routes: <i, k> in Origins) X[<i,j,k>] - sum(<i,j,k> in Routes : <j,k> in Destinations) X[<i,j,k>] ==0;
    
    forall (k in K, <i, k> in I)
      ct_5:  
      sum(<i,j,k> in Routes) X[<i,j,k>] - sum(<j,i,k> in Routes) X[<j, i, k>]==0;
      
    forall (i in NP, h in K diff Ksign) 
      ct_5p:  
      sum(<j,i,h> in Routes) X[<j,i,h>] - sum(<h,k> in Bom, <i,j,k> in Routes) X[<i, j, k>]==0;
                    
    
	forall (<i,j,k> in Routes, <i,k> in NK, <j,k> in NK)
	  ct_6:
	  w[<i,k>] + S[i] + T[<i,j,k>] - w[<j,k>] <= (1 - u[<i,j,k>])*M;
	 
	// production times should be multiplied by the total produced quantity
	forall (<h,k> in Bom, <dh, h> in Destinations)
	  ct_6p:
	     w[<dh,h>] + S[dh] + lts[k] - w[<dh,k>] <= 0; 
	
	
	     
	/*  
	OLD
	forall (i in N, k in K)
	  ct_6_1:
	  (sum (<i,j,k> in Routes)X[<i,j,k>])*A[i] - w[i][k]<=0;

	forall (i in N, k in K)
	  ct_6_2:
	  w[i][k] - (sum (<i,j,k> in Routes)X[<i,j,k>])*B[i] <=0;
	  */	  	
 
	forall ( <i,k> in Origins  union Destinations)
	  ct_8p:
	  w[<i,k>] <= L;
	  
	forall ( <i,k> in Origins  union Destinations)
	  ct_8:
	   w[<i,k>]>= E;
	   

	
	forall (<i,j,k> in Routes)
	  ct_9:
	  X[<i,j,k>] <= Capacity[<i,j>]*u[<i,j,k>]; 
	 
	forall (<i,k> in Origins)
	  ct_10:
	 sum(<i,j,k> in Routes)X[<i,j,k>] <= CapacityP[<i,k>] * z[<i,k>]; 	     	  
		 	  	           
	forall ( <i,k> in NK)
	  	  ct_11a:
	   w[<i,k>]>= 0;    	   
  		
  }   
  

   
   execute DISPLAY {
 writeln("Z\t", Z);
  writeln("Z_TransCost in MEur \t", Z_TransCost/1000.0);
   writeln("z_ProdCost in MEur \t", z_ProdCost/1000.0);
    writeln("z_EmisFact in MEur \t", z_EmisFact/1000.0);
    /*
    for (var destination in N)
    	for (var ks in Ksign){
    	  writeln("ks: ", ks);
    	  writeln("destination: ", destination);
     		writeln("w[destination][ks]", w[destination][ks]);
     }  
     */   		
    writeln("alfa\t", alfa);

    
   writeln("\nconstraint ct9 (capacity) ROUTE, NAME, UB, LB, DUAL, SLACK");
   for(var c in Routes)
    writeln(c.i,"-",c.j,"-",c.k,"\t", ct_9[c.i][c.j][c.k].name," ",ct_9[c.i][c.j][c.k].UB," ",ct_9[c.i][c.j][c.k].LB," ",ct_9[c.i][c.j][c.k].dual," ",ct_9[c.i][c.j][c.k].slack); 
   
      writeln("constraint ct10 (Production capacity) ROUTE, NAME, UB, LB, DUAL, SLACK");
   for(var o in Origins)
    writeln(o.i,"-",o.k,"\t", ct_10[o.i][o.k].name," ",ct_10[o.i][o.k].UB," ",ct_10[o.i][o.k].LB," ",ct_10[o.i][o.k].dual," ",ct_10[o.i][o.k].slack);
  }

   