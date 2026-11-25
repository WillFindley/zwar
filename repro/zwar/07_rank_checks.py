#!/usr/bin/env python3
"""Check the all-time ranks quoted in the paper (Section 6, Tables 7-11).

Universe: every player in B-Ref's season WAR files.
  * Position play: position-player WAR (rounded to 0.1 as published on B-Ref);
    PA from the JAWS pages where listed, otherwise summed season PA; exposure
    floor max(PA, 1).
  * Pitching: pitching WAR (rounded to 0.1 as published on B-Ref); career BF
    from the JAWS pages (1,000 pitchers) or a cached player page, otherwise
    IPouts x 4.2/3 (an approximation that only affects low-ranked pitchers).
  * Unified: the signed two-coordinate statistic, Equation (10); alpha = 0.2 uses the
    value-consistent l_gamma rule (common.z2d_lgamma, gamma = 1/(1 - alpha)), which equals
    Equation (10) at alpha = 1/2 and total WAR at alpha = 0.
The universe is built by zwar/universe.py (shared with 17_leaderboards.py).
Also checks every Z_0.2 value and every rank (alpha = 0, 0.2, 0.5) printed in
the alpha = 1/5 leaderboards drafted by 17_leaderboards.py (TABLES_A02,
SUBPOOL_A02, TWOWAY_A02): Z_0.2 values within display rounding (0.005), Z
ranks exact (0 diff), WAR ranks within the tie block.
Outputs: outputs/rank_check.csv, outputs/rank_alpha02.csv, outputs/rank_tables_a02.csv
"""
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import load_jaws, load_war_daily, z2d, z2d_alpha, z2d_lgamma, write_csv  # noqa: E402
import universe  # noqa: E402

# Value point of the family (gamma = 1.25, Proposition 4 / Section 4)
ALPHA_VALUE = 0.2
# Ranks under alpha = 0.2 quoted in the paper: {(coordinate, pid): rank}. Unified ranks use the
# l_gamma two-coordinate rule (common.z2d_lgamma), as in the alpha = 1/5 tables.
PAPER_A02 = {
    ("pos", "ruthba01"): 1, ("pos", "bondsba01"): 2, ("pos", "mayswi01"): 3,
    ("pos", "cobbty01"): 4, ("pos", "hornsro01"): 7, ("pos", "speaktr01"): 6,
    ("pos", "willite01"): 10, ("pos", "wagneho01"): 8, ("pos", "aaronha01"): 5,
    ("pos", "gehrilo01"): 12, ("pos", "musiast01"): 9, ("pos", "collied01"): 11,
    ("pos", "mantlmi01"): 14, ("pos", "troutmi01"): 21, ("pos", "dimagjo01"): 39,
    ("pos", "steartu99"): 109, ("pos", "robinja02"): 70, ("pos", "gibsojo99"): 197,
    ("pos", "rosepe01"): 61, ("pitch", "johnswa01"): 2, ("pitch", "clemero02"): 3,
    ("pitch", "youngcy01"): 1, ("pitch", "grovele01"): 5, ("pitch", "nichoki01"): 4,
    ("pitch", "alexape01"): 6, ("pitch", "martipe02"): 11, ("pitch", "johnsra05"): 7,
    ("pitch", "seaveto01"): 8, ("pitch", "kershcl01"): 20, ("pitch", "maddugr01"): 9,
    ("pitch", "mathech01"): 10, ("pitch", "fostebi99"): 92, ("pitch", "paigesa01"): 83,
    ("pitch", "ryanno01"): 28, ("pitch", "riverma01"): 34, ("pitch", "koufasa01"): 77,
    ("pitch", "eckerde01"): 53, ("pitch", "wilheho01"): 90, ("pitch", "maricju01"): 57,
    ("pitch", "fellebo01"): 49, ("pitch", "bunniji01"): 67, ("pitch", "gossari01"): 131,
    ("pitch", "fordwh01"): 87, ("pitch", "suttodo01"): 54, ("pitch", "wagnebi02"): 245,
    ("pitch", "chapmar01"): 275, ("pitch", "nathajo01"): 276, ("pitch", "papeljo01"): 320,
    ("pitch", "hillejo01"): 228, ("pitch", "hoffmtr01"): 258, ("pitch", "henketo01"): 348,
    ("pitch", "smithle02"): 257, ("pitch", "janseke01"): 312, ("pitch", "kimbrcr01"): 365,
    ("pitch", "suttebr01"): 346, ("pitch", "wynnea01"): 124, ("pitch", "morrija02"): 177,
    ("unified", "ruthba01"): 1, ("unified", "johnswa01"): 5, ("unified", "troutmi01"): 27,
    ("unified", "clemero02"): 13, ("unified", "youngcy01"): 7, ("unified", "grovele01"): 26,
    ("unified", "steartu99"): 144, ("unified", "robinja02"): 99, ("unified", "nichoki01"): 24,
    ("unified", "alexape01"): 23, ("unified", "martipe02"): 51, ("unified", "gibsojo99"): 286,
    ("unified", "riverma01"): 148, ("unified", "johnsra05"): 36, ("unified", "seaveto01"): 30,
    ("unified", "mathech01"): 33, ("unified", "kershcl01"): 60, ("unified", "maddugr01"): 35,
    ("unified", "ohtansh01"): 175, ("unified", "roganbu99"): 192, ("unified", "rosepe01"): 88,
    ("unified", "bondsba01"): 2, ("unified", "mayswi01"): 3, ("unified", "cobbty01"): 4, ("unified", "hornsro01"): 9, ("unified", "speaktr01"): 8, ("unified", "willite01"): 12, ("unified", "wagneho01"): 10, ("unified", "aaronha01"): 6, ("unified", "gehrilo01"): 15, ("unified", "musiast01"): 11, ("unified", "collied01"): 14, ("unified", "mantlmi01"): 17, ("unified", "schmimi01"): 20, ("unified", "rodrial01"): 16, ("unified", "lajoina01"): 19, ("unified", "ottme01"): 18, ("unified", "robinfr02"): 22
}

# (label, coordinate, paper Z-rank, paper WAR-rank or None, pid)
CHECKS = [
    # Table 7 (position play)
    ("Babe Ruth", "pos", 1, 2, "ruthba01"), ("Barry Bonds", "pos", 2, 1, "bondsba01"),
    ("Willie Mays", "pos", 3, 3, "mayswi01"), ("Ty Cobb", "pos", 4, 4, "cobbty01"),
    ("Rogers Hornsby", "pos", 5, 9, "hornsro01"), ("Tris Speaker", "pos", 6, 6, "speaktr01"),
    ("Ted Williams", "pos", 7, 11, "willite01"), ("Honus Wagner", "pos", 8, 7, "wagneho01"),
    ("Hank Aaron", "pos", 9, 5, "aaronha01"), ("Lou Gehrig", "pos", 10, 13, "gehrilo01"),
    ("Stan Musial", "pos", 11, 8, "musiast01"), ("Eddie Collins", "pos", 12, 10, "collied01"),
    ("Mickey Mantle", "pos", 13, 16, "mantlmi01"), ("Mike Trout", "pos", 18, 30, "troutmi01"),
    ("Joe DiMaggio", "pos", 27, 43, "dimagjo01"), ("Turkey Stearnes", "pos", 39, 166, "steartu99"),
    ("Jackie Robinson", "pos", 40, 106, "robinja02"), ("Josh Gibson", "pos", 50, 345, "gibsojo99"),
    ("Pete Rose", "pos", 143, 41, "rosepe01"),
    # Table 8 (starting pitchers; ranks among all pitchers)
    ("Walter Johnson", "pitch", 1, 2, "johnswa01"), ("Roger Clemens", "pitch", 2, 3, "clemero02"),
    ("Cy Young", "pitch", 3, 1, "youngcy01"), ("Lefty Grove", "pitch", 4, 6, "grovele01"),
    ("Kid Nichols", "pitch", 5, 4, "nichoki01"), ("Grover Alexander", "pitch", 6, 5, "alexape01"),
    ("Pedro Martinez", "pitch", 7, 17, "martipe02"), ("Randy Johnson", "pitch", 8, 9, "johnsra05"),
    ("Tom Seaver", "pitch", 10, 7, "seaveto01"), ("Clayton Kershaw", "pitch", 11, 28, "kershcl01"),
    ("Greg Maddux", "pitch", 12, 8, "maddugr01"), ("Christy Mathewson", "pitch", 13, 10, "mathech01"),
    ("Bill Foster", "pitch", 34, 132, "fostebi99"), ("Satchel Paige", "pitch", 39, 112, "paigesa01"),
    ("Nolan Ryan", "pitch", 46, 20, "ryanno01"),
    # Table 9 (relievers and benchmarks)
    ("Mariano Rivera", "pitch", 9, 80, "riverma01"), ("Sandy Koufax", "pitch", 50, 90, "koufasa01"),
    ("Dennis Eckersley", "pitch", 52, 54, "eckerde01"), ("Hoyt Wilhelm", "pitch", 62, 108, "wilheho01"),
    ("Juan Marichal", "pitch", 63, 56, "maricju01"), ("Bob Feller", "pitch", 69, 46, "fellebo01"),
    ("Jim Bunning", "pitch", 88, 65, "bunniji01"), ("Rich Gossage", "pitch", 90, 169, "gossari01"),
    ("Whitey Ford", "pitch", 95, 86, "fordwh01"), ("Don Sutton", "pitch", 99, 35, "suttodo01"),
    ("Billy Wagner", "pitch", 100, 339, "wagnebi02"), ("Aroldis Chapman", "pitch", 120, 373, "chapmar01"),
    ("Joe Nathan", "pitch", 125, 370, "nathajo01"), ("Jonathan Papelbon", "pitch", 127, 457, "papeljo01"),
    ("John Hiller", "pitch", 128, 278, "hillejo01"), ("Trevor Hoffman", "pitch", 132, 334, "hoffmtr01"),
    ("Tom Henke", "pitch", 146, 465, "henketo01"), ("Lee Smith", "pitch", 164, 314, "smithle02"),
    ("Kenley Jansen", "pitch", 169, 412, "janseke01"), ("Craig Kimbrel", "pitch", 203, 478, "kimbrcr01"),
    ("Bruce Sutter", "pitch", 222, 428, "suttebr01"), ("Early Wynn", "pitch", 226, 96, "wynnea01"),
    ("Jack Morris", "pitch", 264, 150, "morrija02"),
    # Unified (Table 11)
    ("Babe Ruth", "unified", 1, None, "ruthba01"), ("Walter Johnson", "unified", 17, None, "johnswa01"),
    ("Mike Trout", "unified", 19, None, "troutmi01"), ("Roger Clemens", "unified", 21, None, "clemero02"),
    ("Cy Young", "unified", 22, None, "youngcy01"), ("Lefty Grove", "unified", 37, None, "grovele01"),
    ("Turkey Stearnes", "unified", 43, None, "steartu99"), ("Jackie Robinson", "unified", 44, None, "robinja02"),
    ("Kid Nichols", "unified", 49, None, "nichoki01"), ("Grover Alexander", "unified", 52, None, "alexape01"),
    ("Pedro Martinez", "unified", 55, None, "martipe02"), ("Josh Gibson", "unified", 57, None, "gibsojo99"),
    ("Mariano Rivera", "unified", 60, None, "riverma01"), ("Randy Johnson", "unified", 61, None, "johnsra05"),
    ("Tom Seaver", "unified", 63, None, "seaveto01"), ("Christy Mathewson", "unified", 72, None, "mathech01"),
    ("Clayton Kershaw", "unified", 73, None, "kershcl01"), ("Greg Maddux", "unified", 79, None, "maddugr01"),
    ("Shohei Ohtani", "unified", 131, None, "ohtansh01"), ("Bullet Rogan", "unified", 161, None, "roganbu99"),
    ("Pete Rose", "unified", 169, None, "rosepe01"),
    ("Barry Bonds", "unified", 2, None, "bondsba01"), ("Willie Mays", "unified", 3, None, "mayswi01"),
    ("Ty Cobb", "unified", 4, None, "cobbty01"), ("Rogers Hornsby", "unified", 5, None, "hornsro01"),
    ("Tris Speaker", "unified", 6, None, "speaktr01"), ("Ted Williams", "unified", 7, None, "willite01"),
    ("Honus Wagner", "unified", 8, None, "wagneho01"), ("Hank Aaron", "unified", 9, None, "aaronha01"),
    ("Lou Gehrig", "unified", 10, None, "gehrilo01"), ("Stan Musial", "unified", 11, None, "musiast01"),
    ("Eddie Collins", "unified", 12, None, "collied01"), ("Mickey Mantle", "unified", 13, None, "mantlmi01"),
    ("Mike Schmidt", "unified", 14, None, "schmimi01"), ("Alex Rodriguez", "unified", 15, None, "rodrial01"),
    ("Nap Lajoie", "unified", 16, None, "lajoina01"), ("Mel Ott", "unified", 18, None, "ottme01"),
    ("Frank Robinson", "unified", 20, None, "robinfr02"),
]

# Values printed in the alpha = 1/5 leaderboards (outputs/tables/tab_*.tex, written by
# 17_leaderboards.py): (coordinate, pid): (Z_0.2 as printed, WAR rank, Z_0.2 rank, Z_0.5 rank).
# WAR ranks are the best rank of the tie block; the unified board uses the l_gamma rule
# (common.z2d_lgamma), whose alpha = 0 score is total career WAR.
TABLES_A02 = {
    ("pos", "ruthba01"): (25.41, 2, 1, 1), ("pos", "bondsba01"): (24.63, 1, 2, 2),
    ("pos", "mayswi01"): (23.66, 3, 3, 3), ("pos", "cobbty01"): (22.49, 4, 4, 4),
    ("pos", "aaronha01"): (21.24, 5, 5, 9), ("pos", "speaktr01"): (20.79, 6, 6, 6),
    ("pos", "hornsro01"): (20.41, 9, 7, 5), ("pos", "wagneho01"): (20.37, 7, 8, 8),
    ("pos", "musiast01"): (19.41, 8, 9, 11), ("pos", "willite01"): (19.37, 11, 10, 7),
    ("pos", "collied01"): (18.88, 10, 11, 12), ("pos", "gehrilo01"): (18.11, 13, 12, 10),
    ("pos", "rodrial01"): (17.88, 12, 13, 15), ("pos", "mantlmi01"): (17.51, 16, 14, 13),
    ("pos", "ottme01"): (17.11, 15, 15, 17), ("pos", "troutmi01"): (15.26, 30, 21, 18),
    ("pos", "dimagjo01"): (13.19, 43, 39, 27), ("pos", "rosepe01"): (11.5, 41, 61, 143),
    ("pos", "robinja02"): (11.27, 106, 70, 40), ("pos", "steartu99"): (10.32, 166, 109, 39),
    ("pos", "gibsojo99"): (8.47, 345, 197, 50), ("pitch", "youngcy01"): (21.17, 1, 1, 3),
    ("pitch", "johnswa01"): (20.78, 2, 2, 1), ("pitch", "clemero02"): (19.09, 3, 3, 2),
    ("pitch", "nichoki01"): (16.24, 4, 4, 5), ("pitch", "grovele01"): (16.21, 6, 5, 4),
    ("pitch", "alexape01"): (15.99, 5, 6, 6), ("pitch", "johnsra05"): (14.74, 9, 7, 8),
    ("pitch", "seaveto01"): (14.72, 7, 8, 10), ("pitch", "maddugr01"): (14.4, 8, 9, 12),
    ("pitch", "mathech01"): (14.03, 10, 10, 13), ("pitch", "martipe02"): (13.29, 17, 11, 7),
    ("pitch", "blylebe01"): (13.2, 12, 12, 17), ("pitch", "niekrph01"): (13.05, 11, 13, 22),
    ("pitch", "perryga01"): (12.59, 13, 14, 24), ("pitch", "spahnwa01"): (12.59, 14, 15, 23),
    ("pitch", "kershcl01"): (12.08, 28, 20, 11), ("pitch", "ryanno01"): (11.26, 20, 28, 46),
    ("pitch", "paigesa01"): (8.21, 112, 83, 39), ("pitch", "fostebi99"): (7.95, 132, 92, 34),
    ("pitch", "riverma01"): (10.21, 80, 34, 9), ("pitch", "fellebo01"): (9.39, 46, 49, 69),
    ("pitch", "eckerde01"): (9.29, 54, 53, 52), ("pitch", "suttodo01"): (9.28, 35, 54, 99),
    ("pitch", "maricju01"): (9.13, 56, 57, 63), ("pitch", "bunniji01"): (8.76, 65, 67, 88),
    ("pitch", "koufasa01"): (8.5, 90, 77, 50), ("pitch", "fordwh01"): (8.06, 86, 87, 95),
    ("pitch", "wilheho01"): (8.02, 108, 90, 62), ("pitch", "wynnea01"): (7.15, 96, 124, 226),
    ("pitch", "gossari01"): (6.98, 169, 131, 90), ("pitch", "morrija02"): (6.28, 150, 177, 264),
    ("pitch", "gordoto01"): (5.66, 223, 222, 228), ("pitch", "hillejo01"): (5.6, 278, 228, 128),
    ("pitch", "wagnebi02"): (5.4, 339, 245, 100), ("pitch", "kindeel01"): (5.37, 282, 248, 192),
    ("pitch", "shantbo01"): (5.31, 262, 255, 243), ("pitch", "smithle02"): (5.26, 314, 257, 164),
    ("pitch", "hoffmtr01"): (5.25, 334, 258, 132), ("pitch", "chapmar01"): (5.09, 373, 275, 120),
    ("pitch", "nathajo01"): (5.09, 370, 276, 125), ("pitch", "janseke01"): (4.74, 412, 312, 169),
    ("pitch", "papeljo01"): (4.72, 457, 320, 127), ("pitch", "suttebr01"): (4.59, 428, 346, 222),
    ("pitch", "henketo01"): (4.58, 465, 348, 146), ("pitch", "kimbrcr01"): (4.44, 478, 365, 203),
    ("unified", "ruthba01"): (27.24, 1, 1, 1), ("unified", "johnswa01"): (22.07, 2, 5, 17),
    ("unified", "ohtansh01"): (9.72, 222, 175, 131), ("unified", "roganbu99"): (9.52, 222, 192, 161),
    ("unified", "ruffire01"): (9.49, 116, 193, 424), ("unified", "ferrewe01"): (9.12, 198, 225, 295),
    ("unified", "wardjo01"): (8.82, 169, 248, 493), ("unified", "carutbo01"): (8.74, 202, 256, 441),
    ("unified", "uhlege01"): (8.21, 248, 314, 491), ("unified", "lemonbo01"): (7.33, 355, 435, 551),
    ("unified", "mullige01"): (6.93, 375, 502, 669), ("unified", "lucasre01"): (6.92, 438, 505, 609),
    ("unified", "smithel01"): (6.81, 486, 524, 570), ("unified", "woodjo02"): (6.74, 542, 537, 536),
    ("unified", "seymocy01"): (6.6, 517, 564, 643), ("unified", "foutzda01"): (5.32, 685, 838, 1280),
    ("unified", "rileed01"): (4.97, 1055, 948, 776), ("unified", "dihigma99"): (4.42, 1355, 1164, 813),
    ("unified", "bondsba01"): (24.63, 4, 2, 2), ("unified", "mayswi01"): (23.66, 5, 3, 3),
    ("unified", "cobbty01"): (22.5, 6, 4, 4), ("unified", "aaronha01"): (21.24, 7, 6, 9),
    ("unified", "youngcy01"): (21.03, 3, 7, 22), ("unified", "speaktr01"): (20.78, 9, 8, 6),
    ("unified", "hornsro01"): (20.41, 12, 9, 5), ("unified", "wagneho01"): (20.37, 10, 10, 8),
    ("unified", "musiast01"): (19.41, 11, 11, 11), ("unified", "willite01"): (19.37, 14, 12, 7),
    ("unified", "clemero02"): (19.14, 8, 13, 21), ("unified", "collied01"): (18.88, 13, 14, 12),
    ("unified", "gehrilo01"): (18.11, 18, 15, 10), ("unified", "rodrial01"): (17.88, 17, 16, 15),
    ("unified", "mantlmi01"): (17.51, 21, 17, 13), ("unified", "ottme01"): (17.11, 20, 18, 18),
    ("unified", "lajoina01"): (17.07, 23, 19, 16), ("unified", "schmimi01"): (16.92, 26, 20, 14),
    ("unified", "henderi01"): (16.64, 19, 21, 23), ("unified", "robinfr02"): (16.45, 24, 22, 20),
    ("unified", "alexape01"): (16.23, 15, 23, 52), ("unified", "nichoki01"): (16.2, 16, 24, 49),
    ("unified", "morgajo02"): (15.55, 31, 25, 25), ("unified", "grovele01"): (15.55, 27, 26, 37),
    ("unified", "troutmi01"): (15.26, 43, 27, 19), ("unified", "seaveto01"): (15.07, 22, 30, 63),
    ("unified", "mathech01"): (14.69, 24, 33, 72), ("unified", "maddugr01"): (14.53, 28, 35, 79),
    ("unified", "johnsra05"): (14.49, 30, 36, 61), ("unified", "martipe02"): (13.06, 57, 51, 55),
    ("unified", "kershcl01"): (12.37, 64, 60, 73), ("unified", "rosepe01"): (11.5, 67, 88, 169),
    ("unified", "robinja02"): (11.27, 153, 99, 44), ("unified", "steartu99"): (10.26, 262, 144, 43),
    ("unified", "riverma01"): (10.21, 238, 148, 60), ("unified", "gibsojo99"): (8.44, 531, 286, 57),
}
# Sub-pool ranks printed in the tables: (pool, pid): (Z_0.2 rank, Z_0.5 rank)
SUBPOOL_A02 = {
    ("sp", "youngcy01"): (1, 3), ("sp", "johnswa01"): (2, 1), ("sp", "clemero02"): (3, 2),
    ("sp", "nichoki01"): (4, 5), ("sp", "grovele01"): (5, 4), ("sp", "alexape01"): (6, 6),
    ("sp", "johnsra05"): (7, 8), ("sp", "seaveto01"): (8, 9), ("sp", "maddugr01"): (9, 11),
    ("sp", "mathech01"): (10, 12), ("sp", "martipe02"): (11, 7), ("sp", "blylebe01"): (12, 16),
    ("sp", "niekrph01"): (13, 21), ("sp", "perryga01"): (14, 23), ("sp", "spahnwa01"): (15, 22),
    ("sp", "kershcl01"): (20, 10), ("sp", "ryanno01"): (28, 45), ("sp", "paigesa01"): (81, 38),
    ("sp", "fostebi99"): (89, 33), ("rp", "riverma01"): (1, 1), ("rp", "eckerde01"): (2, 2),
    ("rp", "wilheho01"): (3, 3), ("rp", "gossari01"): (4, 4), ("rp", "gordoto01"): (5, 20),
    ("rp", "hillejo01"): (6, 9), ("rp", "wagnebi02"): (7, 5), ("rp", "kindeel01"): (8, 14),
    ("rp", "shantbo01"): (9, 22), ("rp", "smithle02"): (10, 12), ("rp", "hoffmtr01"): (11, 10),
    ("rp", "chapmar01"): (13, 6), ("rp", "nathajo01"): (14, 7), ("rp", "janseke01"): (17, 13),
    ("rp", "papeljo01"): (20, 8), ("rp", "suttebr01"): (25, 19), ("rp", "henketo01"): (27, 11),
    ("rp", "kimbrcr01"): (28, 15),
}
# Two-way table (players with >= 10 WAR in both coordinates; l_gamma rule):
# pid: (Zpos_0.2, Zpitch_0.2, Zpool_0.2, Z2D_0.2, rank among 18 at 0.2, at 0.5)
TWOWAY_A02 = {
    "ruthba01": (25.41, 3.73, 26.52, 27.24, 1, 1), "johnswa01": (2.71, 20.78, 22.06, 22.07, 2, 2),
    "ohtansh01": (7.01, 4.06, 9.72, 9.72, 3, 3), "roganbu99": (4.35, 6.53, 9.49, 9.52, 4, 4),
    "ruffire01": (2.86, 7.75, 9.39, 9.49, 5, 6), "ferrewe01": (2.68, 7.51, 9.05, 9.12, 6, 5),
    "wardjo01": (5.67, 4.44, 8.77, 8.82, 7, 9), "carutbo01": (3.0, 6.85, 8.73, 8.74, 8, 7),
    "uhlege01": (2.45, 6.72, 8.13, 8.21, 9, 8), "lemonbo01": (2.54, 5.72, 7.2, 7.33, 10, 11),
    "mullige01": (2.89, 5.0, 6.72, 6.93, 11, 15), "lucasre01": (2.74, 5.12, 6.8, 6.92, 12, 13),
    "smithel01": (5.39, 2.27, 6.68, 6.81, 13, 12), "woodjo02": (2.22, 5.36, 6.74, 6.74, 14, 10),
    "seymocy01": (5.47, 1.89, 6.5, 6.6, 15, 14), "foutzda01": (2.34, 3.72, 5.32, 5.32, 16, 18),
    "rileed01": (2.67, 3.03, 4.95, 4.97, 17, 16), "dihigma99": (2.81, 2.26, 4.41, 4.42, 18, 17),
}

# Hypothetical scores placed into the all-pitcher ranking (Section 3.7)
VALUE_CHECKS = [
    ("Skenes 0.386", 17.1 / np.sqrt(1959), 200), ("Gooden 2-yr 0.401", 17.7 / np.sqrt(1944), 162),
    ("Gooden 5-yr 0.427", 29.3 / np.sqrt(4718), 131), ("Gooden peak 0.467", 48.3 / np.sqrt(10706), 98),
    ("Gooden career 0.446", 48.2 / np.sqrt(11705), 113), ("Lincecum 3-yr 0.353", 17.5 / np.sqrt(2451), 251),
    ("Lincecum peak 0.376", 24.5 / np.sqrt(4248), 220),
]


def main():
    u = universe.build()
    pids, bat, pitch = u["pids"], u["bat"], u["pitch"]
    pos_w, pos_n, pit_w, pit_n, approx = u["pos_w"], u["pos_n"], u["pit_w"], u["pit_n"], u["approx"]

    ranking, tie_range = universe.ranking, universe.tie_range

    zpos = {p: pos_w[p] / np.sqrt(max(pos_n[p], 1)) for p in pids if p in bat}
    zpit = {p: pit_w[p] / np.sqrt(max(pit_n[p], 1)) for p in pids if p in pitch}
    zuni = {p: z2d(pos_w[p], pos_n[p], pit_w[p], pit_n[p]) for p in pids}
    r_zpos, _ = ranking(zpos)
    r_zpit, order_pit = ranking(zpit)
    r_zuni, _ = ranking(zuni)
    wpos_pool = {p: pos_w[p] for p in zpos}
    wpit_pool = {p: pit_w[p] for p in zpit}
    r_wpos, _ = ranking(wpos_pool)
    r_wpit, _ = ranking(wpit_pool)

    rows, bad = [], 0
    for label, coord, zr, wr, pid in CHECKS:
        if coord == "pos":
            ours_z, ours_w = r_zpos.get(pid), r_wpos.get(pid)
            w_lo, w_hi = tie_range(wpos_pool, pid)
        elif coord == "pitch":
            ours_z, ours_w = r_zpit.get(pid), r_wpit.get(pid)
            w_lo, w_hi = tie_range(wpit_pool, pid)
        else:
            ours_z, ours_w = r_zuni.get(pid), None
            w_lo, w_hi = 0, 0
        dz = abs(ours_z - zr) if ours_z else None
        w_ok = True if not wr else (w_lo <= wr <= w_hi)
        flag = "OK" if (dz == 0 and w_ok) else "CHECK"
        bad += flag != "OK"
        rows.append([label, coord, zr, ours_z, wr or "", ours_w or "", flag])
        if flag != "OK":
            print(f"CHECK {label:18s} {coord:7s} Z-rank paper {zr} ours {ours_z}; "
                  f"WAR-rank paper {wr} ours {ours_w} (tie {w_lo}-{w_hi})")
    zs = np.array([zpit[p] for p in order_pit])
    for label, v, paper_rank in VALUE_CHECKS:
        ours = int((zs > v).sum()) + 1
        rows.append([label, "pitch value", paper_rank, ours, "", "", "approx"])
        print(f"{label:22s} would rank #{ours} among pitchers (paper ~#{paper_rank})")
    assert r_zpos["washihe01"] == len(zpos) == 23659 and abs(zpos["washihe01"] + 0.5) < 1e-12
    print(f"Herb Washington Z_1/2={zpos['washihe01']:.3f} ranks #{r_zpos['washihe01']}/{len(zpos)}")
    best_approx = min((r_zpit[p] for p in approx if p in r_zpit), default=None)
    print(f"{len(CHECKS)} rank checks, {bad} mismatches; "
          f"{len(approx)} pitchers use approximate BF (best such Z_pitch rank: #{best_approx})")
    write_csv("rank_check.csv", ["player", "coordinate", "paper_Z_rank", "ours_Z_rank",
                                 "paper_WAR_rank", "ours_WAR_rank", "status"], rows)

    # ------------------------------------------------------------------
    # Value point of the family, alpha = 0.2 (gamma = 1.25): all-time ranks
    # quoted in the Z_0.2 columns of Tables 3-5 and 7.
    # ------------------------------------------------------------------
    a = ALPHA_VALUE
    zpos_a = {p: pos_w[p] / max(pos_n[p], 1) ** a for p in zpos}
    zpit_a = {p: pit_w[p] / max(pit_n[p], 1) ** a for p in zpit}
    zuni_a = {p: z2d_lgamma(pos_w[p], pos_n[p], pit_w[p], pit_n[p], a) for p in pids}
    # The l_gamma rule reproduces Equation (10) at alpha = 1/2 and total WAR at alpha = 0
    assert max(abs(z2d_lgamma(pos_w[p], pos_n[p], pit_w[p], pit_n[p], 0.5) - zuni[p]) for p in pids) < 1e-12
    assert max(abs(z2d_lgamma(pos_w[p], pos_n[p], pit_w[p], pit_n[p], 0.0) - pos_w[p] - pit_w[p])
               for p in pids) < 1e-9
    r_pos_a, order_pos_a = ranking(zpos_a)
    r_pit_a, order_pit_a = ranking(zpit_a)
    r_uni_a, order_uni_a = ranking(zuni_a)
    best_approx_a02 = min(((r_pit_a[p], p) for p in approx if p in r_pit_a), default=None)
    assert best_approx_a02 is not None and best_approx_a02[0] > 370, (
        f"Expected no approx pitcher in top 370 at alpha=0.2, got {best_approx_a02}")
    assert r_pit_a["skenepa01"] == 494 and abs(round(zpit_a["skenepa01"], 2) - 3.75) < 1e-12
    print(f"alpha = {a}: best approx-BF pitcher rank #{best_approx_a02[0]} ({best_approx_a02[1]} > 370); "
          f"Skenes Z_0.2={zpit_a['skenepa01']:.2f} (#{r_pit_a['skenepa01']})")
    a_rows, a_bad = [], 0
    for label, coord, _, _, pid in CHECKS:
        r = {"pos": r_pos_a, "pitch": r_pit_a, "unified": r_uni_a}[coord].get(pid)
        paper = PAPER_A02.get((coord, pid))
        ok = paper is None or r == paper
        a_bad += not ok
        a_rows.append([label, coord, paper if paper is not None else "", r, "OK" if ok else "CHECK"])
        if not ok:
            print(f"CHECK alpha={a} {label:18s} {coord:7s} paper {paper} ours {r}")
    n_quoted = sum(1 for k in PAPER_A02)
    print(f"alpha = {a}: {n_quoted} quoted ranks checked, {a_bad} mismatches")
    for name, order, sc in [("position play", order_pos_a, zpos_a), ("pitching", order_pit_a, zpit_a),
                            ("unified", order_uni_a, zuni_a)]:
        load = load_war_daily("bat")
        loadp = load_war_daily("pitch")
        nm = lambda p: (load.get(p) or loadp.get(p))["name"]  # noqa: E731
        print(f"  alpha = {a} top 15 ({name}): " + "; ".join(
            f"{i + 1} {nm(p)} {sc[p]:.2f}" for i, p in enumerate(order[:15])))
    write_csv("rank_alpha02.csv", ["player", "coordinate", "paper_rank_alpha0.2",
                                   "ours_rank_alpha0.2", "status"], a_rows)
    _, order_uni = ranking(zuni)
    expected_uni_pit = {"alpha = 0.5": [3, 5, 13], f"alpha = {a}": [5, 11, 28]}
    for lab, order in [("alpha = 0.5", order_uni), (f"alpha = {a}", order_uni_a)]:
        counts = []
        for k in (25, 50, 100):
            counts.append(sum(1 for p in order[:k] if pit_w[p] > pos_w[p]))
        assert counts == expected_uni_pit[lab], f"Unexpected unified pitcher counts {lab}: {counts}"
        print(f"  unified {lab}: pitchers (pitching WAR > position WAR) in top 25/50/100: "
              + "/".join(map(str, counts)))

    # Section 6.3 claim: Rivera's 9.05 WAR/820 BF is the highest career rate among all pitchers >= 2,000 BF
    rate_top = max((pit_w[p] / (pit_n[p] / 820.0), p) for p in zpit if pit_n[p] >= 2000)
    assert rate_top[1] == "riverma01" and abs(round(rate_top[0], 2) - 9.05) < 1e-12, f"Top rate >=2000 BF: {rate_top}"
    # Section 6.2 & App. H claim: Kershaw (#20) 0.10 tie block spans #17-#21 (Keefe, Mussina, Verlander, Kershaw, Schilling)
    assert order_pit_a[16:21] == ["keefeti01", "mussimi01", "verlaju01", "kershcl01", "schilcu01"]
    assert universe.tie_range(zpit_a, "kershcl01", eps=0.10) == (17, 21)

    # ------------------------------------------------------------------
    # alpha = 1/5 leaderboards (17_leaderboards.py): every printed Z_0.2 value
    # and every printed rank at alpha = 0, 0.2 and 0.5.
    # ------------------------------------------------------------------
    zsc = {"pos": (zpos_a, zpos), "pitch": (zpit_a, zpit), "unified": (zuni_a, zuni)}
    wsc = {"pos": wpos_pool, "pitch": wpit_pool, "unified": {p: pos_w[p] + pit_w[p] for p in pids}}
    rk = {"pos": (r_pos_a, r_zpos), "pitch": (r_pit_a, r_zpit), "unified": (r_uni_a, r_zuni)}
    t_rows, t_bad, t_exact = [], 0, 0

    def t_check(table, pid, field, paper, ours, ok, exact):
        nonlocal t_bad, t_exact
        t_bad += not ok
        t_exact += exact
        t_rows.append([table, pid, field, paper, ours, "OK" if ok else "CHECK"])
        if not ok:
            print(f"CHECK alpha=1/5 table {table:8s} {pid:10s} {field:10s} printed {paper} ours {ours}")

    for (coord, pid), (z_shown, r_war, r02, r05) in TABLES_A02.items():
        za, zh = zsc[coord]
        ra, rh = rk[coord]
        z = za[pid]
        t_check(coord, pid, "Z0.2", z_shown, round(z, 4), abs(z - z_shown) <= 0.005 + 1e-9,
                f"{z:.2f}" == f"{z_shown:.2f}")
        lo, hi = tie_range(wsc[coord], pid)
        t_check(coord, pid, "WAR rank", r_war, f"{lo}-{hi}" if hi > lo else lo, lo <= r_war <= hi,
                r_war == lo)
        t_check(coord, pid, "Z0.2 rank", r02, ra[pid], ra[pid] == r02, ra[pid] == r02)
        t_check(coord, pid, "Z0.5 rank", r05, rh[pid], rh[pid] == r05, rh[pid] == r05)

    sp_pool = [d["pid"] for d in load_jaws("SP") if d["IPouts"] >= 4500]   # >= 1,500 IP
    rp_pool = [d["pid"] for d in load_jaws("RP")]
    two_pool = [p for p in pids if pos_w[p] >= 10 and pit_w[p] >= 10]
    sub = {}
    for name, pool, sc in [("sp", sp_pool, (zpit_a, zpit)), ("rp", rp_pool, (zpit_a, zpit)),
                           ("twoway", two_pool, (zuni_a, zuni))]:
        sub[name] = tuple(ranking({p: s[p] for p in pool})[0] for s in sc)
    for (pool, pid), (r02, r05) in SUBPOOL_A02.items():
        o2, o5 = sub[pool][0][pid], sub[pool][1][pid]
        t_check(pool, pid, "Z0.2 rank", r02, o2, o2 == r02, o2 == r02)
        t_check(pool, pid, "Z0.5 rank", r05, o5, o5 == r05, o5 == r05)
    if len(two_pool) != len(TWOWAY_A02):
        print(f"CHECK two-way pool has {len(two_pool)} players, table {len(TWOWAY_A02)}")
        t_bad += 1
    a = ALPHA_VALUE
    for pid, (zp, zt, zpl, z2, r02, r05) in TWOWAY_A02.items():
        pool_v = (pos_w[pid] + pit_w[pid]) / max(pos_n[pid] + pit_n[pid], 1) ** a
        assert z2d_alpha(pos_w[pid], pos_n[pid], pit_w[pid], pit_n[pid], a) < pool_v, (
            f"Expected quadrature < pool for {pid} at alpha={a}")
        for field, shown, ours in [("Zpos0.2", zp, zpos_a[pid]), ("Zpitch0.2", zt, zpit_a[pid]),
                                   ("Zpool0.2", zpl, pool_v), ("Z2D0.2", z2, zuni_a[pid])]:
            t_check("twoway", pid, field, shown, round(ours, 4), abs(ours - shown) <= 0.005 + 1e-9,
                    f"{ours:.2f}" == f"{shown:.2f}")
        o2, o5 = sub["twoway"][0][pid], sub["twoway"][1][pid]
        t_check("twoway", pid, "rank18 0.2", r02, o2, o2 == r02, o2 == r02)
        t_check("twoway", pid, "rank18 0.5", r05, o5, o5 == r05, o5 == r05)
    print(f"alpha = 1/5 tables: {len(t_rows)} printed values checked, {t_bad} outside tolerance, "
          f"{t_exact} exact")
    write_csv("rank_tables_a02.csv", ["table", "pid", "field", "printed", "ours", "status"], t_rows)
    if bad or a_bad or t_bad:
        sys.exit(1)




if __name__ == "__main__":
    main()
