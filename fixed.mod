# By Yihsu Chen and Sepehr Ramyar 
# Prosumer model linked to wholesale and capacity markets
# This model assumes fixed capacity for new units
###############################################################################
# Sets used to define the problem                                             #
###############################################################################

set F;						# Firms

set I ordered;				# Nodes in the network
set J ordered;
set K;						# within I cross I;
							# Arcs (interfaces) in the transmission network
set P;						# Plants
set H{F,I} within P;		# Set of Plants for firm F at node I
set M;						# set of technologies owned by presumer
set N{I} within M;			# set of technologies own by presumer in i

set T;						# set of time periods: peak, off-peak
set VV;
set V{F,I} within VV;						# set of new generation technologies
param co2{i in I};
###############################################################################
# Parameters                                                                  #
###############################################################################
param p0{I,T};			# vertical intercept for demand
param q0{I,T};			# horizontal intercept for demand

param PTDF{K, I}; 		# PTDF matrix
param b0{P};			# constant term in supply curve
param b1{P};			# slope term in supply curve

param cap{P};			# gen cap
param Tcap{K};			# transmission cap

param st{I};			# strategy index of presumer
#param stf{F};			# strategy index of firms

param tau{I};			# adjusting prosumer marginal benefit of consumption

param B{T};				# number of hours in each period
###############################################################################
# prosumer parameters														  #
###############################################################################
param pcap{M};			# production capacity owned by prosumer
param pmc0{M};			# prosumer marginal production cost
param pmc1{M};			# prosumer marginal production cost
param p2{I,T};			# vertical intercept of prosumer; A^0 in the doc
param q2{I,T};			# horizontal intercept  of prosumer; E^0 in the doc
###############################################################################
# Variables in the problem                                                    #
###############################################################################
var x{f in F, i in I, h in H[f,i], t in T} >= 0;	# Output of plant
var w{I,T};											# Wheeling charge
var s{f in F, i in I, t in T} >=0;					# sales
var y{I,T};											# injection/withdraw
var ph{T};											# hub price
var a{I,T};											# arbitrage 

###############################################################################
# prosumer variables:
###############################################################################
var zs{f in F,i in I, t in T} >=0;			# sale  of prosumer to wholesale market
var zb{f in F,i in I, t in T} >=0;			# buy of prosumer to wholesale market
var delta{I,T} >=0;							# dual for prosumer min load satisfaction at node i
var g{I,T} >=0;								# output by dispatchable plants owned by presumer
var l{I,T} >=0;								# consumption
var z{ f in F, i in I, t in T} = zs[f,i,t]-zb[f,i,t];
###############################################################################
# Mutipliers for variational inequality constraints                           #
###############################################################################
var theta{F,T};												# dual for mass balanced
var rho{f in F, i in I, h in H[f,i], t in T} >= 0;			# dual for gen capacity constriant
var lambda_up{k in K, t in T} >= 0;							# upper transmission limit
var lambda_lo{k in K, t in T} >= 0;							# lower transmission limit
var miu{i in I, t in T} >=0;								# dual of sell 
var kappa{i in I, t in T} >= 0;								# dual on dispatchable unit

###############################################################################
# capacity market elements                         							  #
###############################################################################
var xnew{f in F, i in I, v in V[f,i], t in T};	# new capacity to be installed
param INV{VV};								# investment cost for capacity
param MCV{VV};								# variable cost of unit of tech {v}
param XCAP{VV};
var rhonew{f in F, i in I, v in V[f,i], t in T};


param pricecap;							# price cap in $/MWh
param D{i in I, t in T} = (p0[i,t]-pricecap)*(q0[i,t]/p0[i,t]) ;						# Demand function kink
param RM;								# reserve margin
var d1{I,T};
var d2{I,T};
#var d{i in I, t in T} = d1[i,t] + d2[i,t];
var xi1{I,T};
var xi2{I,T};
###############################################################################
# Defined variables                                                           #
###############################################################################
#var d{i in I,t in T} = d1[i,t] + d2[i,t] - D[i,t];
var d{i in I, t in T} = sum{f in F} s[f,i,t];# +a[i,t];#-sum{f in F} zb[i,f];
#var p{i in I, t in T} = p0[i,t]- (p0[i,t]/q0[i,t])*d[i,t]; # price at node i
var p{I,T} >= 0;
var mc {f in F, i in I, h in H[f,i],t in T} = b0[h] + 2*b1[h]* (x[f,i,h,t]);			# Marginal cost 
var mc1{i in I, t in T} = pmc0[2] + pmc1[2]*g[i,t];
var flow {k in K, t in T} = sum {i in I} (PTDF[k,i]*y[i,t]);	 						# Flow definition
var ps{f in F, t in T} = (1/1000)*(   sum{i in I}( (p[i,t] - w[i,t])*(s[f,i,t] - zs[f,i,t] + zb[f,i,t]) ) - sum{i in I, h in H[f,i]}(   x[f,i,h,t]*b0[h] + (x[f,i,h,t]^2)*b1[h] - w[i,t]*x[f,i,h,t]   )	- sum{i in I, v in V[f,i]}(  MCV[v]*xnew[f,i,v,t] - w[i,t]*xnew[f,i,v,t]   )		);
#var ps{f in F} = (1/1000)*(sum{i in I} (p[i]-w[i])*s[f,i]-sum{i in I, h in H[f,i]} b1[h]*x[f,i,h]);
#var ps{f in F} = (sum{i in I} (p[i]-w[i])*s[f,i]-sum{i in I, h in H[f,i]} ((mc[f,i,h]-w[i])*x[f,i,h]))/1000;
#var ps{f in F} = (sum{i in I} (p[i]-w[i])*s[f,i]-sum{i in I, h in H[f,i]} (x[f,i,h]*b0[h] + (x[f,i,h]^2)*b1[h]))/1000;
var cs{t in T} =    (1/1000)* sum{i in I} (p0[i,t]*d[i,t] - 0.5*(p0[i,t]/q0[i,t])*(d[i,t]**2) - p[i,t]*d[i,t] ) ;	# consumer surplus
var iso{t in T} = (1/1000)*sum{i in I} w[i,t]*y[i,t];									# iso revenu
#var arb =sum{i in I,t in T} B[t]*a[i,t]*(p[i,t]-w[i,t])/1000;
var ts{i in I, t in T}=sum{f in F} s[f,i,t];										# total sales
var totd{t in T} =sum{i in I} d[i,t];
var avgp{t in T} =sum{i in I} (p[i,t]*d[i,t])/totd[t];
var mb{i in I, t in T} = tau[i]*p2[i,t]-p2[i,t]/q2[i,t]*(pcap[1]+g[i,t]);
var tx{i in I, t in T} = sum{f in F, h in H[f,i]} (x[f,i,h,t]); 
var tzs{i in I, t in T} = sum{f in F} zs[f,i,t];
var tzb{i in I, t in T} = sum{f in F} zb[f,i,t];
#var tzs{i in I, t in T} =  zs[i,1,t];
#var tzb{i in I, t in T} =  zb[i,1,t];
var tz{i in I, t in T} = tzs[i,t]- tzb[i,t];
#var pres = (sum{i in I} p[i]*(tz[i]) - sum{i in I} (p2[i]*(pcap[1]-l[i])-0.5*p2[i]/q2[i]*(pcap[1]**2-l[i]**2))-pmc0[1]*pcap[1]-sum{i in I}(pmc0[2]*g[i]+0.5*pmc1[2]*g[i]**2))/1000; 		#presumers profit
var pres{t in T} = (1/1000)*(sum{i in I} p[i,t]*(tz[i,t]) + sum{i in I} (tau[i]*p2[i,t]*l[i,t] - 0.5*(p2[i,t]/q2[i,t])*(l[i,t]^2)) -sum{i in I}(pmc0[2]*g[i,t]+0.5*pmc1[2]*g[i,t]**2)); 		#presumers profit
var txt{t in T} = sum{i in I} tx[i,t];
#var swp = pres + sw;

var primal{t in T} = (1/1000)* sum{i in I} ( p[i,t]*(tz[i,t]) + p2[1,t]*l[i,t] - (0.5)*(p2[i,t]/q2[i,t])*(l[i,t]^2) - (pmc0[2]*g[i,t]+0.5*pmc1[2]*g[i,t]**2));

#var ps{f in F} = (1/1000)*(sum{t in T}B[t]*(sum{i in I} (p[i,t]-w[i,t])*(s[f,i,t] - tz[i,t])-sum{i in I, h in H[f,i]} ((b0[h]-w[i,t])*x[f,i,h,t]+b1[h]*x[f,i,h,t]**2))
#				 -sum{i in I, v in V[f,i],t in T}B[t]*((MCV[v]-w[i,t])*xnew[f,i,v,t])	- sum{i in I, v in V[f,i]}(xcap[f,i,v]*INV[v]) + caprice*(sum{i in I, h in H[f,i]}cap[h] + sum{i in I, v in V[f,i]}xcap[f,i,v])	);

var ps_sum{f in F} = sum{t in T}ps[f,t];
var tps = sum{f in F} ps_sum[f]; 

var sw{t in T} = cs[t] + sum{f in F} ps[f,t] + iso[t];											# social surplus

#var producer = sum{f in F, i in I, h in H[f,i]}( p[i]*x[f,i,h]) - sum{i in I, f in F, h in H[f,i]} b1[h]*x[f,i,h];
#var producer = sum{f in F, i in I, h in H[f,i]}( p[i]*x[f,i,h]) - sum{i in I, f in F, h in H[f,i]} (b0[h]*x[f,i,h] + b1[h]*(x[f,i,h]^2));
#var producer2 = sum {f in F} (sum{i in I} (p[i])*s[f,i]-sum{i in I, h in H[f,i]} ((mc[f,i,h])*x[f,i,h]))/1000;

var dpeak = sum{i in I}d[i,'peak'];

##############################################################################
# prosumer KKT:																  #
###############################################################################

subject to prosumer_zs {i in I, f in F, t in T: ord(i)==1}:
	0 <= zs[f,i,t] complements B[t]*p[i,t] - delta[i,t] <= 0;	

subject to prosumer_zs1 {i in I,f in F, t in T: ord(i)<>1}:
	zs[f,i,t] = 0;

subject to prosumer_zb {i in I,f in F, t in T: ord(i)==1}:
	0 <= zb[f,i,t] complements -B[t]*p[i,t] + delta[i,t] <= 0;	

subject to prosumer_zb1 {i in I, f in F, t in T: ord(i)<>1}:
	zb[f,i,t] = 0;
	
subject to foc_l{i in I, t in T: ord(i)==1}:
	0 <= l[i,t] complements B[t]*(p2[i,t]-(p2[i,t]/q2[i,t])*l[i,t]) - delta[i,t] <= 0;
	
subject to foc_l1{i in I, t in T: ord(i)<>1}:
	l[i,t] =0;		

subject to prosumer_load {i in I, t in T}:
	0 <= delta[i,t] complements l[i,t] - pcap[1]-g[i,t]  + tz[i,t] <= 0;						#>>>>>>>>>>> pcap[1,t] <> K_t for prosumer renewable capacity

subject to gcap{i in I, t in T:ord(i)==1}:
	0 <= kappa[i,t] complements g[i,t] - pcap[2] <= 0;

subject to gcap1{i in I, t in T:ord(i)<>1}:
	0 <= kappa[i,t] complements g[i,t] <= 0;
	
subject to output{i in I, t in T}:
	0 <= g[i,t] complements -B[t]*mc1[i,t] - kappa[i,t] + delta[i,t] <=0;
	



	
###############################################################################
# producer                                                                       #
###############################################################################

subject to prod_sur {f in F, i in I, t in T}: 
	0 <= s[f,i,t] complements  B[t]*(p[i,t] - w[i,t]) - theta [f,t] <= 0;


subject to prod_x {f in F, i in I, h in H[f,i], t in T}: 
	0 <= x[f,i,h,t] complements B[t]*( - mc[f,i,h,t] + w[i,t]) - rho[f,i,h,t] +theta[f,t] <= 0;
	
subject to prod_xnew {f in F, i in I, v in V[f,i], t in T}: 
	0 <= xnew[f,i,v,t] complements B[t]*( - MCV[v] + w[i,t]) - rhonew[f,i,v,t] +theta[f,t] <= 0;

subject to prod_cap {f in F, i in I, h in H[f,i], t in T}:
	0 <= rho[f,i,h,t] complements x[f,i,h,t] - cap[h] <= 0; 		#>>>>>>>>> WORTH CONSIDERING IN TERMS OF ORGANIZING *H* and *H^new*

subject to prod_capnew {f in F, i in I, v in V[f,i], t in T}:
	0 <= rhonew[f,i,v,t] complements xnew[f,i,v,t] - XCAP[v] <= 0;        

subject to gen_sale_balance {f in F, t in T}: # proper care is needed when calculating surplus
	sum {i in I} (s[f,i,t] - z[f,i,t]) - sum{i in I, h in H[f,i]} x[f,i,h,t] - sum{i in I, v in V[f,i]}xnew[f,i,v,t] = 0;

#subject to gen_sale_balance {i in I, f in F, t in T}: # proper care is needed when calculating surplus
#	s[f,i,t] - (zs[f,i,t] - zb[f,i,t]) - sum{h in H[f,i]} x[f,i,h,t] - sum{v in V[f,i]}xnew[f,i,v,t] = 0;


#subject to gen_sale_balance {f in F, t in T}: # proper care is needed when calculating surplus
#	sum {i in I} (s[f,i,t] - tz[i,t]) - sum{i in I, h in H[f,i]} x[f,i,h,t] - sum{i in I, v in V[f,i]}xnew[f,i,v,t] = 0;


	
###############################################################################
# HOBBS PAPER FOR PARAMETER TABLE 2, J. REG. ECON. 		FOR CAP INVST		  #
###############################################################################

##############################################################################
# Grid Owner KKT														  #
###############################################################################                  

subject to flow_upper{k in K, t in T}:
 	0 <= lambda_up[k,t] complements flow[k,t] - Tcap[k] <= 0;

subject to flow_lower{k in K, t in T}: 	
	0 <= lambda_lo[k,t] complements -flow[k,t] - Tcap[k] <= 0;

subject to injection {i in I, t in T}:
	  B[t]*w[i,t] + sum{k in K} (PTDF[k,i]*(lambda_lo[k,t]-lambda_up[k,t])) = 0;
	  

	


###############################################################################
# balance	:																  #
###############################################################################

subject to nodalbalance {i in I, t in T}:
	y[i,t] = - sum{f in F, h in H[f,i]}x[f,i,h,t] - sum{f in F, v in V[f,i]}xnew[f,i,v,t] + sum{f in F} s[f,i,t] - tz[i,t];		 #tz[i,t] used to be sum{f in F} (zs[f,i,t]-zb[f,i,t])

#subject to genoffset {f in F, t in T}:
#	sum{i in I}(s[f,i,t] - tz[i,t]) - sum{i in I, h in H[f,i]}x[f,i,h,t] - sum{i in I, v in V[f,i]} xnew[f,i,v,t] = 0;


#subject to yzero{t in T}:
#	sum{i in I} y[i,t] = 0;


###############################################################################
# demand:																	  #
###############################################################################




subject to demand1{i in I, t in T}:
	0 <= d1[i,t] complements pricecap - p[i,t] - xi1[i,t] <= 0;

subject to demand2{i in I, t in T}:
	0 <= (d2[i,t] - D[i,t]) complements p0[i,t] - (p0[i,t]/q0[i,t])*d2[i,t] - p[i,t] - xi2[i,t] <= 0;

subject to xi_1{i in I, t in T}:
	0 <= xi1[i,t] complements d1[i,t] - D[i,t] <= 0;
	
subject to xi_2{i in I, t in T}:
	0 <= xi2[i,t] complements d2[i,t] - q0[i,t] <= 0;

subject to demands{i in I, t in T}:
	d[i,t] = d1[i,t] + d2[i,t] - D[i,t];
	
subject to DnS{i in I, t in T}:
	d[i,t] = sum{f in F} s[f,i,t];


/*
*/

#subject to demand2{i in I, t in T}:
#	0 <= d[i,t] complements p0[i,t] - (p0[i,t]/q0[i,t])*d[i,t] - p[i,t] <= 0;




###############################################################################
# capacity market:															  #
###############################################################################
/*
subject to capacity_market:
	0 <= caprice complements sum{f in F, i in I, h in H[f,i]}cap[h]+ sum{f in F, i in I, v in V[f,i]}xcap[f,i,v] - sum{i in I}d[i,'peak']*(1+RM) >= 0    #>>>>>>>>>>>>>>. This is H[f,i]^{new} 
*/


###############################################################################
# arbitrager demand:															  #
###############################################################################

/*
subject to foc_a{i in I}:
	p[i]-w[i] = ph;
	
subject to foc_ph:
	sum{i in I} a[i] = 0;	
*/
