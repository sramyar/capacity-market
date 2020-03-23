# By Yihsu Chen and Sepehr Ramyar 
# Title: A Oligopoly Power Market Model in Presence of Strategic Presumers #? 
# A presumer model that links to the wholesale. 
# presumer is assumed to own two types of units: non-dipatachable renewable and dispatch one 
# presumer is allowed to sell and purchase from the wholesale 
# depends on its net position, either exercise monoposony or monopoly power
# wholesale is likely to benefit from its action when it is in short position: down-size its procurement to lower power prices,
# leaving more power to wholesale; however, when it is in long position: withhold capacity leading to higher power prices
# leading to worse off outcomes at wholesale.  
# other questions: size?  
# note that presumer's variables are sell (zs >=0) and buy (zb>=0)
 
 
###############################################################################
# Sets used to define the problem                                             #
###############################################################################

set F;						# Firms
#set Fs within F;			# Stackelberg leaders
#set Fc within F;			# Cournot follower firms
#set Fp within F;			# Price-taker follower firms
#set Ff := Fc union Fp;		# All followers
set I ordered;				# Nodes in the network
set J ordered;
set K;						# within I cross I;
							# Arcs (interfaces) in the transmission network
set P;						# Plants
set H{F,I} within P;		# Set of Plants for firm F at node I
set M;						# set of technologies owned by presumer
set N{I} within M;			# set of technologies own by presumer in i


###############################################################################
# Parameters                                                                  #
###############################################################################
param p0{I};			# vertical intercept
param q0{I};			# horizontal intercept
param p2{I};			# vertical intercept of presumers
param q2{I};			# horizontal intercept  of presumers
param PTDF{K, I}; 		# PTDF matrix
param co2cap;			# co2 cap
param b0{P};			# constant term in supply curve
param b1{P};			# slope term in supply curve
param co2{P};			# co2 rate
param cap{P};			# gen cap
param Tcap{K};			# transmission cap
param cc;				# cap coverage index
param st{I};			# strategy index of presumer
param stf{F};			# strategy index of firms

param tau{I};			# adjusting prosumer marginal benefit of consumption


###############################################################################
# prosumer parameters														  #
###############################################################################
param pcap{M};			# production capacity owned by prosumer
param pmc0{M};			# prosumer marginal production cost
param pmc1{M};			# prosumer marginal production cost

###############################################################################
# Variables in the problem                                                    #
###############################################################################
var x{f in F, i in I, h in H[f,i]} >= 0;	# Output of plant
var w{I};									# Wheeling charge
#var aa{I};									# arbitrage quantity
var s{f in F, i in I} >=0;					# sales
var y{I};									# injection/withdraw
var ph;										# hub price
var a{I};									# arbitrage 

###############################################################################
# prosumer variables:
###############################################################################
var zs{i in I,f in F} >=0;			# sale  of prosumer to wholesale market
var zb{i in I,f in F} >=0;			# buy of prosumer to wholesale market
var delta{I} >=0;		# dual for prosumer min load satisfaction at node i
var g{I} >=0;			# output by dispatchable plants owned by presumer
var l{I} >=0;			# consumption

###############################################################################
# Mutipliers for variational inequality constraints                           #
###############################################################################
var theta{F};								# dual for mass balanced
var rho{f in F, i in I, h in H[f,i]} >= 0;	# dual for gen capacity constriant
var lambda_up{k in K} >= 0;					# upper transmission limit
var lambda_lo{k in K} >= 0;					# lower transmission limit
var miu{i in I} >=0;						# dual of sell 
var kappa{i in I} >= 0;						# dual on dispatchable unit


###############################################################################
# Defined variables                                                           #
###############################################################################
var d{i in I} = sum{f in F} s[f,i]+a[i];#-sum{f in F} zb[i,f];
var p{i in I} = p0[i]- ((p0[i]/q0[i]*d[i])); # price at node i
var mc {f in F, i in I, h in H[f,i]} = b0[h] + 2*b1[h]* (x[f,i,h]);			# Marginal cost 
var mc1{i in I} = pmc0[2] + pmc1[2]*g[i];
var flow {k in K} = sum {i in I} (PTDF[k,i]*y[i]);	 						# Flow definition
#var ps{f in F} = (1/1000)*(sum{i in I} (p[i]-w[i])*s[f,i]-sum{i in I, h in H[f,i]} b1[h]*x[f,i,h]);
#var ps{f in F} = (sum{i in I} (p[i]-w[i])*s[f,i]-sum{i in I, h in H[f,i]} ((mc[f,i,h]-w[i])*x[f,i,h]))/1000;
#var ps{f in F} = (sum{i in I} (p[i]-w[i])*s[f,i]-sum{i in I, h in H[f,i]} (x[f,i,h]*b0[h] + (x[f,i,h]^2)*b1[h]))/1000;
var ps{f in F} = (1/1000)*(sum{i in I} (p[i]-w[i])*s[f,i]-sum{i in I, h in H[f,i]} ((b0[h]-w[i])*x[f,i,h]+b1[h]*x[f,i,h]**2));
var cs =  sum{i in I} (p0[i]*d[i] - 0.5*p0[i]/q0[i]*d[i]**2 - p[i]*d[i])/1000;	# consumer surplus
var iso = sum{i in I} w[i]*y[i]/1000;											# iso revenu
var arb =sum{i in I} a[i]*(p[i]-w[i])/1000;
var sw = cs + sum{f in F} ps[f] + iso;											# social surplus
var tps = sum{f in F} ps[f]; 
var ts{i in I}=sum{f in F} s[f,i];										# total sales
var totd =sum{i in I} d[i];
var avgp =sum{i in I} (p[i]*d[i])/totd;
var mb{i in I} = tau[i]*p2[i]-p2[i]/q2[i]*(pcap[1]+g[i]);
var tx{i in I} = sum{f in F, h in H[f,i]} (x[f,i,h]); 
var tzs{i in I} = sum{f in F} zs[i,f];
var tzb{i in I} = sum{f in F} zb[i,f];
var tz{i in I} = tzs[i]- tzb[i];
#var pres = (sum{i in I} p[i]*(tz[i]) - sum{i in I} (p2[i]*(pcap[1]-l[i])-0.5*p2[i]/q2[i]*(pcap[1]**2-l[i]**2))-pmc0[1]*pcap[1]-sum{i in I}(pmc0[2]*g[i]+0.5*pmc1[2]*g[i]**2))/1000; 		#presumers profit
var pres = (sum{i in I} p[i]*(tz[i]) + sum{i in I} (tau[i]*p2[i]*l[i] - 0.5*(p2[i]/q2[i])*(l[i]^2)) -sum{i in I}(pmc0[2]*g[i]+0.5*pmc1[2]*g[i]**2))/1000; 		#presumers profit
var txt = sum{i in I} tx[i];
var swp = pres + sw;
var primal =  sum{i in I} ( p[i]*(tz[i]) + p2[1]*l[i] - (0.5)*(p2[i]/q2[i])*(l[i]^2) - (pmc0[2]*g[i]+0.5*pmc1[2]*g[i]**2));
#var producer = sum{f in F, i in I, h in H[f,i]}( p[i]*x[f,i,h]) - sum{i in I, f in F, h in H[f,i]} b1[h]*x[f,i,h];
#var producer = sum{f in F, i in I, h in H[f,i]}( p[i]*x[f,i,h]) - sum{i in I, f in F, h in H[f,i]} (b0[h]*x[f,i,h] + b1[h]*(x[f,i,h]^2));
#var producer2 = sum {f in F} (sum{i in I} (p[i])*s[f,i]-sum{i in I, h in H[f,i]} ((mc[f,i,h])*x[f,i,h]))/1000;

###############################################################################
# Model                                                                       #
###############################################################################

subject to prod_sur {f in F, i in I}: 
	0 <= s[f,i] complements  p[i] - (p0[i]/q0[i])*s[f,i]*stf[f] - w[i] - theta [f] <= 0;

subject to prod_x {f in F, i in I, h in H[f,i]}: 
	0 <= x[f,i,h] complements  - mc[f,i,h] + w[i] - rho[f,i,h] +theta[f] <= 0;

subject to gen_sale_balance {f in F}: # proper care is needed when calculating surplus
	sum{i in I, h in H[f,i]} x[f,i,h] - sum {i in I} (s[f,i] +zb[i,f]-zs[i,f]) = 0;

subject to prod_cap {f in F, i in I, h in H[f,i]}:
	0 <= rho[f,i,h] complements x[f,i,h] - cap[h] <= 0;             

subject to flow_upper{k in K}:
 	0 <= lambda_up[k] complements flow[k] - Tcap[k] <= 0;

subject to flow_lower{k in K}: 	
	0 <= lambda_lo[k] complements -flow[k] - Tcap[k] <= 0;

subject to injection {i in I}:
	  w[i] + sum{k in K} (PTDF[k,i]*(lambda_lo[k]-lambda_up[k])) = 0;

subject to nodalbalance {i in I}:
	y[i]= sum{f in F, h in H[f,i]} (-x[f,i,h]) + d[i] - sum{f in F} (zs[i,f]-zb[i,f]);		

##############################################################################
# prosumer KKT:																  #
###############################################################################

subject to prosumer_zs {i in I, f in F: ord(i)==1}:
	0 <= zs[i,f] complements p[i] - p0[i]/q0[i]*tz[i]*st[i] -delta[i]+ miu[i] <= 0;	

subject to prosumer_zs1 {i in I,f in F: ord(i)<>1}:
	zs[i,f] = 0;

subject to prosumer_zb {i in I,f in F: ord(i)==1}:
	0 <= zb[i,f] complements -p[i] + (p0[i]/q0[i])*tz[i]*st[i] + delta[i]- miu[i] <= 0;	

subject to prosumer_zb1 {i in I, f in F: ord(i)<>1}:
	zb[i,f] = 0;
	
subject to foc_l{i in I: ord(i)==1}:
	0 <= l[i] complements tau[i]*p2[i]-(p2[i]/q2[i])*l[i]-delta[i] + miu[i] <= 0;
	
subject to foc_l1{i in I: ord(i)<>1}:
	l[i] =0;		

subject to prosumer_load {i in I}:
	0 <= delta[i] complements l[i] - pcap[1]-g[i]  + tz[i] <= 0;		

subject to gcap{i in I:ord(i)==1}:
	0 <= kappa[i] complements g[i] -pcap[2] <= 0;

subject to gcap1{i in I:ord(i)<>1}:
	0 <= kappa[i] complements g[i] <= 0;
	
subject to output{i in I}:
	0 <= g[i] complements -mc1[i] - kappa[i] + delta[i] <=0;

subject to sell{i in I}:
	0 <= miu[i] complements  -tz[i]- l[i] <=0;		

	
###############################################################################
# arbitrager demand:															  #
###############################################################################
subject to foc_a{i in I}:
	p[i]-w[i] = ph;
	
subject to foc_ph:
	sum{i in I} a[i] = 0;	
	
	
