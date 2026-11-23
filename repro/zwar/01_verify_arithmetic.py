#!/usr/bin/env python3
"""Recompute every derived number in zwar_paper.tex from the paper's own
inputs (Z scores, rates per 650 PA / 820 BF, BF/IP, two-coordinate and pooled
scores, percentage changes, checkpoint values, gaps and rounding bounds).

Prints each check; exits with status 1 if any value disagrees with the paper.
"""
import math
import sys
s = math.sqrt
FAILS = []
def ip(x):
    w = int(x); f = round((x - w) * 10)
    return w + f / 3
def chk(label, got, exp, tol):
    bad = abs(got - exp) > tol
    if bad:
        FAILS.append(label)
    flag = "   <-- MISMATCH" if bad else ""
    print(f"{label:45s} computed={got:.4f} paper={exp}{flag}")

print("== Hitters (Zpos, rate/650)")
H = [("Ruth",162.3,10628,9.93,1.574),("Bonds",162.8,12606,8.39,1.450),("Mays",156.2,12545,8.09,1.395),
     ("Cobb",149.8,13103,7.43,1.309),("Hornsby",127.4,9481,8.73,1.308),("Speaker",136.1,12021,7.36,1.241),
     ("Williams",121.7,9792,8.08,1.230),("Wagner",132.8,11777,7.33,1.224),("Aaron",143.2,13941,6.68,1.213),
     ("Gehrig",113.5,9665,7.63,1.155),("Musial",128.5,12721,6.57,1.139),("Collins",123.7,12087,6.65,1.125),
     ("Mantle",110.3,9910,7.23,1.108),("Trout",91.7,7837,7.61,1.036),("DiMaggio",78.9,7672,6.68,0.901),
     ("Stearnes",55.2,4378,8.20,0.834),("JRobinson",64.1,5955,7.00,0.831),("Gibson",41.1,2683,9.96,0.793),
     ("Rose",79.6,15890,3.26,0.631),("Schmidt",106.9,10062,None,1.066),("ARod",117.4,12207,None,1.063),
     ("Lajoie",108.7,10471,None,1.062),("Ott",110.7,11347,None,1.039),("FRobinson",107.2,11744,None,0.989)]
for n,w,pa,r,z in H:
    if r: chk(n+" rate", w/pa*650, r, 0.006)
    chk(n+" Z", w/s(pa), z, 0.0006)

print("== Pitchers (Zpitch, rate/820, BF/IP)")
P = [("WJohnson",155.4,23415,5914.1,5.44,1.016),("Clemens",138.7,20240,4916.2,5.62,0.975),
     ("Young",165.9,29565,7356.0,4.60,0.965),("Grove",113.2,16622,3940.2,5.58,0.878),
     ("Nichols",119.0,21099,5067.1,4.62,0.819),("Alexander",116.9,20893,5190.0,4.59,0.809),
     ("Pedro",86.1,11394,2827.1,6.20,0.807),("RJohnson",103.5,17067,4135.1,4.97,0.792),
     ("Seaver",106.0,19369,4783.0,4.49,0.762),("Kershaw",78.1,11279,2855.1,5.68,0.735),
     ("Maddux",104.8,20421,5008.1,4.21,0.733),("Mathewson",100.6,18929,4788.2,4.36,0.731),
     ("Foster",45.6,6213,1509.0,6.02,0.579),("Paige",48.7,7331,1800.0,5.45,0.569),("Ryan",83.6,22575,5386.0,3.04,0.556),
     ("Rivera",56.3,5103,1283.2,9.05,0.788),("Koufax",53.1,9497,2324.1,4.58,0.545),("Eck",62.3,13534,3285.2,3.77,0.536),
     ("Wilhelm",49.7,9164,2254.1,4.45,0.519),("Marichal",61.8,14236,3507.0,3.56,0.518),("Feller",65.2,16180,3827.0,3.30,0.513),
     ("Bunning",60.4,15618,3760.1,3.17,0.483),("Gossage",41.6,7507,1809.1,4.54,0.480),("Ford",53.6,13036,3170.1,3.37,0.469),
     ("Sutton",68.3,21631,5282.1,2.59,0.464),("BWagner",27.8,3600,903.0,6.33,0.463),("Chapman",26.1,3554,873.0,6.02,0.438),
     ("Nathan",26.4,3771,923.1,5.74,0.430),("Papelbon",23.3,2938,725.2,6.50,0.430),("Hiller",31.0,5206,1242.0,4.88,0.430),
     ("Hoffman",28.1,4388,1089.1,5.25,0.424),("Henke",23.0,3194,789.2,5.90,0.407),("LSmith",29.3,5388,1289.1,4.46,0.399),
     ("Jansen",24.7,3860,972.1,5.25,0.398),("Kimbrel",22.7,3502,867.2,5.32,0.384),("Sutter",24.4,4251,1042.0,4.71,0.374),
     ("Wynn",51.5,19408,4564.0,2.18,0.370),("Morris",43.6,16120,3824.0,2.22,0.343)]
for n,w,bf,i,r,z in P:
    chk(n+" rate", w/bf*820, r, 0.006)
    chk(n+" Z", w/s(bf), z, 0.0006)
    print(f"{'':45s} BF/IP={bf/ip(i):.3f}")

def z2d(wp,pa,wq,bf):
    I = wp*abs(wp)/max(pa,1) + wq*abs(wq)/max(bf,1)
    return math.copysign(s(abs(I)), I)
def zpool(wp,pa,wq,bf): return (wp+wq)/s(max(pa+bf,1))
print("== Two-way")
T = [("Ruth",162.3,10628,20.4,4896,1.466,1.601),("WJohnson",13.0,2534,155.4,23415,1.045,1.048),
     ("Ohtani",38.4,4947,19.4,2479,0.671,0.671),("Rogan",20.5,2326,37.3,6063,0.631,0.640),
     ("Ferrell",11.3,1345,48.8,11568,0.529,0.548),("Ruffing",13.2,2084,55.3,18546,0.477,0.498),
     ("Caruthers",14.8,2906,44.7,11842,0.490,0.494),("Ward",34.3,8114,28.1,10164,0.462,0.472),
     ("Dihigo",12.4,1673,10.0,1702,0.386,0.388)]
for n,a,b,c,d,zp,z2 in T:
    m = max(a/s(b), c/s(d))
    chk(n+" Zpool", zpool(a,b,c,d), zp, 0.0006)
    chk(n+" Z2D", z2d(a,b,c,d), z2, 0.0006)
    print(f"{'':45s} dPool={100*(zpool(a,b,c,d)/m-1):+.1f}%  d2D={100*(z2d(a,b,c,d)/m-1):+.1f}%")
chk("Uhle Z2D (45.0 pitch WAR)", z2d(10.6,1514,45.0,13597), 0.472, 0.0006)
chk("Uhle Z2D (45.1 pitch footer)", z2d(10.6,1514,45.1,13597), 0.473, 0.0006)

print("== Unified / negative secondary")
U = [("Cobb",149.8,13103,0.1,20,1.309),("Speaker",136.1,12021,-0.1,4,1.240),("Clemens",0.6,213,138.7,20240,0.976),
     ("Young",-2.2,3107,165.9,29565,0.964),("Grove",-6.5,1580,113.2,16622,0.863),("Stearnes",55.2,4378,-0.4,37,0.832),
     ("Nichols",-0.8,2265,119.0,21099,0.819),("Alexander",3.0,1982,116.9,20893,0.812),("Pedro",-2.2,518,86.1,11394,0.801),
     ("Gibson",41.1,2683,-0.2,10,0.791),("Rivera",0.0,4,56.3,5103,0.788),("RJohnson",-2.5,691,103.5,17067,0.787),
     ("Seaver",3.9,1552,106.0,19369,0.768),("Mathewson",6.6,1900,100.6,18929,0.747),("Kershaw",2.8,847,78.1,11279,0.742),
     ("Maddux",1.8,1812,104.8,20421,0.735),("Wallace",70.4,9635,6.0,1799,0.731)]
for n,a,b,c,d,z in U:
    chk(n+" unified", z2d(a,b,c,d), z, 0.0006)
chk("Young pooled", zpool(-2.2,3107,165.9,29565), 0.906, 0.0006)

print("== Text claims")
chk("Pujols Z* thru 2012", 91.4/s(8103), 1.015, 0.0006)
chk("Pujols full", 101.3/s(13041), 0.887, 0.0006)
chk("Pujols late rate /650", 9.9/4938*650, 1.30, 0.006)
chk("Pujols rate thru 2012", 91.4/8103*650, 7.33, 0.006)
xp = 4938/8103
chk("Pujols finite threshold frac", (s(1+xp)-1)/xp, 0.441, 0.0006)
chk("Pujols finite threshold /650", (s(1+xp)-1)/xp*91.4/8103*650, 3.23, 0.006)
chk("Leverage-implied noise ratio (1+1.667)/(1+1.294)", 2.667/2.294, 1.16, 0.005)
chk("fWAR shift W. Johnson (about 0.25)", 1.016-0.761, 0.25, 0.006)
chk("Griffey Z*", 76.2/s(7319), 0.891, 0.0006)
chk("Griffey full", 83.8/s(11304), 0.78818, 0.000006)
chk("Rivera exact", 56.3/s(5103), 0.78813, 0.000006)
w2 = 121.7*(9792+2000)/9792
chk("Williams +2000 WAR", w2, 146.6, 0.06); chk("Williams +2000 Z", w2/s(11792), 1.350, 0.0006)
chk("Ruth split", s(30**2/2500 + 132.3**2/8128), 1.585, 0.0006)
x = 4896/10628
chk("Ruth finite threshold frac", (s(1+x)-1)/x, 0.453, 0.0006)
chk("Ruth pitch/bat rate ratio", (20.4/4896)/(162.3/10628), 0.273, 0.0006)
rb, rp = 38.4/4947, 19.4/2479
chk("Ohtani rate diff %", 100*(rp/rb-1), 0.82, 0.006)
chk("Ohtani Lagrange gap x1e6", 1e6*4947*2479/(4947+2479)*(rb-rp)**2, 6.6, 0.06)
chk("WJ * 59/41 (bWAR equal-pool factor)", 155.4/s(23415)*59/41, 1.461, 0.0006)
chk("WJ * 59/41, two-coordinate", math.sqrt((155.4/s(23415)*59/41)**2 + 13.0**2/2534), 1.484, 0.0006)
chk("Rivera/Eck %", 100*((56.3/s(5103))/(62.3/s(13534))-1), 47.2, 0.06)
chk("Skenes Z", 17.1/s(1959), 0.386, 0.0006); chk("Skenes rate", 17.1/1959*820, 7.16, 0.006)
chk("Gooden 2yr", 17.7/s(1944), 0.401, 0.0006); chk("Gooden rate", 17.7/1944*820, 7.47, 0.006)
chk("Gooden 5yr", 29.3/s(4718), 0.427, 0.0006); chk("Gooden peak", 48.3/s(10706), 0.467, 0.0006)
chk("Gooden final 48.2", 48.2/s(11705), 0.446, 0.0006); chk("Gooden final 48.4 (summed displayed seasons)", 48.4/s(11705), 0.447, 0.0006)
xg = 8762/1944
chk("Gooden 86-98 rate exceeds threshold (ratio>1)", float((30.6/8762)/((s(1+xg)-1)/xg*17.7/1944) > 1), 1, 0)
chk("Lincecum 3yr", 17.5/s(2451), 0.353, 0.0006); chk("Lincecum peak", 24.5/s(4248), 0.376, 0.0006)
chk("Lincecum rate", 24.5/4248*820, 4.73, 0.006); chk("Lincecum final", 19.9/s(7120), 0.236, 0.0006)
chk("Kershaw WAR/sqrt(IP)", 78.1/s(ip(2855.1)), 1.462, 0.0006); chk("Maddux WAR/sqrt(IP)", 104.8/s(ip(5008.1)), 1.481, 0.0006)
chk("Cobb-Hornsby Zpos gap", 149.8/s(13103)-127.4/s(9481), 0.0003, 0.00005)
chk("Cobb-Hornsby 2D gap", z2d(149.8,13103,0.1,20)-127.4/s(9481), 0.0004, 0.00005)
chk("Rivera-RJ 2D gap", z2d(0,4,56.3,5103)-z2d(-2.5,691,103.5,17067), 0.0016, 0.00005)
chk("Alexander-Pedro gap", 116.9/s(20893)-86.1/s(11394), 0.002, 0.0005)
chk("Kershaw-Mathewson gap below 0.005", float(78.1/s(11279)-100.6/s(18929) < 0.005), 1, 0)
for n,N in [("Rivera",5103),("Kershaw",11279),("RJ",17067),("Maddux",20421)]:
    print(f"rounding +/-0.05/sqrt(N) {n}: {0.05/s(N):.5f}")
print("sigma range", 1.5/s(650), 2.0/s(650), " => z for ZWAR=1:", s(650)/2.0, s(650)/1.5)
for a in [0.3]:
    print("alpha=0.3 Ruth vs Bonds", 162.3/10628**a, 162.8/12606**a)

chk("Young batting Z", -2.2/s(3107), -0.039, 0.0006)
chk("Grove batting Z", -6.5/s(1580), -0.164, 0.0006)
chk("RJ batting Z", -2.5/s(691), -0.095, 0.0006)
chk("Ruffing/Ferrell bat:pitch ratio ~0.7", (13.2/s(2084))/(55.3/s(18546)), 0.71, 0.01)
chk("Ferrell bat:pitch ratio", (11.3/s(1345))/(48.8/s(11568)), 0.68, 0.01)
chk("sigma calibration: 0.43 runs x sqrt(650) / 10", 0.43*s(650)/10, 1.1, 0.05)
chk("Brouthers neg pitching shift", 79.8/s(7691) - z2d(79.8,7691,-1.1,127), 0.0053, 0.00006)

from scipy.stats import norm
sig = 0.065
for name, wp, pa, wq, bf, exp_2s, exp_1s in [
    ("Ruth", 162.3, 10628, 20.4, 4896, 0.6, 0.7),
    ("Ohtani", 38.4, 4947, 19.4, 2479, 2.4, 3.1),
    ("Rogan", 20.5, 2326, 37.3, 6063, 2.6, 3.3),
    ("Dihigo", 12.4, 1673, 10.0, 1702, 5.7, 7.7),
]:
    z = z2d(wp, pa, wq, bf)
    p = math.exp(-0.5 * (z / sig) ** 2)
    z_2s = -norm.ppf(0.5 * p) * sig
    z_1s = -norm.ppf(p) * sig
    chk(f"chi2_2 -> chi2_1 (2-sided) shrink % {name}", 100 * (1 - z_2s / z), exp_2s, 0.06)
    chk(f"chi2_2 -> 1-sided normal shrink % {name}", 100 * (1 - z_1s / z), exp_1s, 0.06)

print("== Value point alpha = 0.2 and seasons vs events (Sections 3.2-3.4, 5, 11)")
chk("10-WAR season in 5-WAR seasons, gamma=1.25", 2 ** 1.25, 2.4, 0.05)
chk("10-WAR season in 5-WAR seasons, gamma=4/3", 2 ** (4 / 3), 2.5, 0.05)
chk("10-WAR / 5-WAR WS gain ratio (0.1047/0.0413)", 0.1047 / 0.0413, 2.5, 0.05)
chk("alpha = 1 - 1/gamma at gamma 1.17", 1 - 1 / 1.17, 0.14, 0.006)
chk("alpha = 1 - 1/gamma at gamma 1.30", 1 - 1 / 1.30, 0.23, 0.006)
chk("alpha=0.2 threshold, Pujols (0.2 x 7.33)", 0.2 * 91.4 / 8103 * 650, 1.5, 0.06)
chk("alpha=0.5 threshold, Pujols (0.5 x 7.33)", 0.5 * 91.4 / 8103 * 650, 3.7, 0.05)
xp = 4938 / 8103
chk("Pujols finite threshold frac, alpha=0.2", ((1 + xp) ** 0.2 - 1) / xp, 0.164, 0.0006)
chk("Pujols finite threshold /650, alpha=0.2", ((1 + xp) ** 0.2 - 1) / xp * 91.4 / 8103 * 650, 1.20, 0.006)
chk("Pujols Z_0.2 through 2012", 91.4 / 8103 ** 0.2, 15.11, 0.006)
chk("Pujols Z_0.2 full career", 101.3 / 13041 ** 0.2, 15.22, 0.006)
chk("reliever vs modern SP factor (750/280)^0.2", (750 / 280) ** 0.2, 1.22, 0.006)
chk("19th-century SP factor (750/2000)^0.2", (750 / 2000) ** 0.2, 0.82, 0.006)
chk("SD ratio 12,000 vs 3,000 events at alpha=0.2", 4 ** 0.3, 1.5, 0.02)
chk("reliever rate multiple at alpha=0.2 (4^0.8)", 4 ** 0.8, 3.0, 0.05)
chk("SD(Z_0.2) at 2,000 events (sigma=0.065)", 0.065 * 2000 ** 0.3, 0.64, 0.006)
chk("SD(Z_0.2) at 20,000 events (sigma=0.065)", 0.065 * 20000 ** 0.3, 1.27, 0.006)
chk("above-average valuation: 8/3", 8 / 3, 2.7, 0.04)
chk("above-average valuation: gamma_eff = log2(8/3)", math.log2(8 / 3), 1.4, 0.02)

def z2d_lgamma(wp, pa, wq, bf, a):
    g = 1.0 / (1.0 - a)
    I = math.copysign(abs(wp) ** g / max(pa, 1) ** (g - 1), wp) + math.copysign(abs(wq) ** g / max(bf, 1) ** (g - 1), wq)
    return math.copysign(abs(I) ** (1.0 / g), I)

for name, wb, nb, wp, np_, e02, e05 in [
    ("Grove", -6.5, 1580, 113.2, 16622, -4.1, -1.7),
    ("R.Johnson", -2.5, 691, 103.5, 17067, -1.7, -0.7),
    ("Pedro", -2.2, 518, 86.1, 11394, -1.8, -0.7),
]:
    chk(f"{name} neg batting drop a=0.2 (%)", 100 * (z2d_lgamma(wb, nb, wp, np_, 0.2) / (wp / np_ ** 0.2) - 1), e02, 0.05)
    chk(f"{name} neg batting drop a=0.5 (%)", 100 * (z2d_lgamma(wb, nb, wp, np_, 0.5) / (wp / np_ ** 0.5) - 1), e05, 0.05)

chk("Z0.2 tolerance N=5,000 (0.005*N^0.3)", 0.005 * 5000 ** 0.3, 0.06, 0.005)
chk("Z0.2 tolerance N=30,000 (0.005*N^0.3)", 0.005 * 30000 ** 0.3, 0.11, 0.005)
chk("Z0.2 pair rounding bound N=5,000", 0.10 / 5000 ** 0.2, 0.018, 0.0005)
chk("Z0.2 pair rounding bound N=30,000", 0.10 / 30000 ** 0.2, 0.013, 0.0005)

def rbound_2d(wp, pa, wq, bf, a=0.2):
    g = 1.0 / (1.0 - a)
    z = abs(z2d_lgamma(wp, pa, wq, bf, a))
    return sum(0.05 * (abs(w) / max(n, 1)) ** (g - 1) * z ** (1 - g)
               for w, n in ((wp, pa), (wq, bf)) if w != 0)

chk("Gibson unified Z0.2 rounding bound", rbound_2d(41.1, 2683, -0.2, 10), 0.0214, 0.0001)
chk("Dihigo unified Z0.2 rounding bound", rbound_2d(12.4, 1673, 10.0, 1702), 0.0197, 0.0001)

# Section 6.2, 6.4, and Appendix F inline arithmetic
chk("Ruth-Bonds PA diff", 12606 - 10628, 1978, 0)
chk("Ruth-Bonds crossover alpha", math.log(162.8 / 162.3) / math.log(12606 / 10628), 0.0180, 0.0005)
fac_w = (9792 + 2000) / 9792
chk("Williams +2000 PA WAR %", 100 * (fac_w - 1), 20.4, 0.5)
chk("Williams +2000 PA Z_0.2 %", 100 * (fac_w ** 0.8 - 1), 16.0, 0.5)
chk("Williams +2000 PA Z_0.5 %", 100 * (fac_w ** 0.5 - 1), 9.7, 0.5)

x_ruth = 4896 / 10628
chk("Ruth pool threshold alpha=0.2", ((1 + x_ruth) ** 0.2 - 1) / x_ruth, 0.171, 0.0006)
chk("Ruth pool lift alpha=0.2 (%)", 100 * (((162.3 + 20.4) / (10628 + 4896) ** 0.2) / (162.3 / 10628 ** 0.2) - 1), 4.4, 0.06)
chk("Ruth 2D lift alpha=0.2 (%)", 100 * (z2d_lgamma(162.3, 10628, 20.4, 4896, 0.2) / (162.3 / 10628 ** 0.2) - 1), 7.2, 0.06)
chk("Ruth pool drop alpha=0.5 (%)", 100 * (zpool(162.3, 10628, 20.4, 4896) / (162.3 / s(10628)) - 1), -6.9, 0.06)
chk("Ruth 2D lift alpha=0.5 (%)", 100 * (z2d(162.3, 10628, 20.4, 4896) / (162.3 / s(10628)) - 1), 1.7, 0.06)

chk("2^0.8 - 1 max 2D lift a=0.2 (%)", 100 * (2 ** 0.8 - 1), 74.1, 0.1)
chk("sqrt(2) - 1 max 2D lift a=0.5 (%)", 100 * (s(2) - 1), 41.4, 0.1)
chk("Ohtani rate diff < 1% (%)", float(100 * abs(rp / rb - 1) < 1.0), 1.0, 0)
chk("Ohtani Z0.2 2D lift (%)", 100 * (z2d_lgamma(38.4, 4947, 19.4, 2479, 0.2) / (38.4 / 4947 ** 0.2) - 1), 38.8, 0.06)
chk("Ohtani Z0.2 pool lift (%)", 100 * (((38.4 + 19.4) / (4947 + 2479) ** 0.2) / (38.4 / 4947 ** 0.2) - 1), 38.8, 0.06)

chk("Herb Washington Z_1/2", -0.5 / s(max(0, 1)), -0.500, 0.0005)
chk("Paul Skenes Z_0.2", 17.1 / 1959 ** 0.2, 3.75, 0.006)

print()
print("ALL CHECKS PASSED" if not FAILS else f"{len(FAILS)} MISMATCHES: {FAILS}")
sys.exit(1 if FAILS else 0)
