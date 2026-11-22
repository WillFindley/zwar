"""Raw inputs exactly as reported in zwar_paper.tex (Tables 7-11 and text).

These are the values the paper claims; 02_verify_inputs.py compares them with
the Baseball-Reference snapshot in data/raw/.
"""

# (name, position-player WAR, career PA)
HITTERS = [
    ("Babe Ruth", 162.3, 10628), ("Barry Bonds", 162.8, 12606),
    ("Willie Mays", 156.2, 12545), ("Ty Cobb", 149.8, 13103),
    ("Rogers Hornsby", 127.4, 9481), ("Tris Speaker", 136.1, 12021),
    ("Ted Williams", 121.7, 9792), ("Honus Wagner", 132.8, 11777),
    ("Hank Aaron", 143.2, 13941), ("Lou Gehrig", 113.5, 9665),
    ("Stan Musial", 128.5, 12721), ("Eddie Collins", 123.7, 12087),
    ("Mickey Mantle", 110.3, 9910), ("Mike Trout", 91.7, 7837),
    ("Joe DiMaggio", 78.9, 7672), ("Turkey Stearnes", 55.2, 4378),
    ("Jackie Robinson", 64.1, 5955), ("Josh Gibson", 41.1, 2683),
    ("Pete Rose", 79.6, 15890), ("Mike Schmidt", 106.9, 10062),
    ("Alex Rodriguez", 117.4, 12207), ("Nap Lajoie", 108.7, 10471),
    ("Mel Ott", 110.7, 11347), ("Frank Robinson", 107.2, 11744),
    ("Ken Griffey Jr.", 83.8, 11304), ("Albert Pujols", 101.3, 13041),
    ("Rickey Henderson", 111.2, 13346), ("Joe Morgan", 100.6, 11329),
    # Small-sample examples in Section 6.6 and Appendix F
    ("Herb Washington", -0.5, 0), ("Ron Wotus", 1.0, 67),
]

# (name, pitching WAR, career BF, career IP)
PITCHERS = [
    ("Walter Johnson", 155.4, 23415, "5914.1"), ("Roger Clemens", 138.7, 20240, "4916.2"),
    ("Cy Young", 165.9, 29565, "7356.0"), ("Lefty Grove", 113.2, 16622, "3940.2"),
    ("Kid Nichols", 119.0, 21099, "5067.1"), ("Pete Alexander", 116.9, 20893, "5190.0"),
    ("Pedro Martinez", 86.1, 11394, "2827.1"), ("Randy Johnson", 103.5, 17067, "4135.1"),
    ("Tom Seaver", 106.0, 19369, "4783.0"), ("Clayton Kershaw", 78.1, 11279, "2855.1"),
    ("Greg Maddux", 104.8, 20421, "5008.1"), ("Christy Mathewson", 100.6, 18929, "4788.2"),
    ("Bill Foster", 45.6, 6213, "1509.0"), ("Satchel Paige", 48.7, 7331, "1800.0"),
    ("Nolan Ryan", 83.6, 22575, "5386.0"), ("Mariano Rivera", 56.3, 5103, "1283.2"),
    ("Sandy Koufax", 53.1, 9497, "2324.1"), ("Dennis Eckersley", 62.3, 13534, "3285.2"),
    ("Hoyt Wilhelm", 49.7, 9164, "2254.1"), ("Juan Marichal", 61.8, 14236, "3507.0"),
    ("Bob Feller", 65.2, 16180, "3827.0"), ("Jim Bunning", 60.4, 15618, "3760.1"),
    ("Goose Gossage", 41.6, 7507, "1809.1"), ("Whitey Ford", 53.6, 13036, "3170.1"),
    ("Don Sutton", 68.3, 21631, "5282.1"), ("Billy Wagner", 27.8, 3600, "903.0"),
    ("Aroldis Chapman", 26.1, 3554, "873.0"), ("Joe Nathan", 26.4, 3771, "923.1"),
    ("Jonathan Papelbon", 23.3, 2938, "725.2"), ("John Hiller", 31.0, 5206, "1242.0"),
    ("Trevor Hoffman", 28.1, 4388, "1089.1"), ("Tom Henke", 23.0, 3194, "789.2"),
    ("Lee Smith", 29.3, 5388, "1289.1"), ("Kenley Jansen", 24.7, 3860, "972.1"),
    ("Craig Kimbrel", 22.7, 3502, "867.2"), ("Bruce Sutter", 24.4, 4251, "1042.0"),
    ("Early Wynn", 51.5, 19408, "4564.0"), ("Jack Morris", 43.6, 16120, "3824.0"),
    ("Paul Skenes", 17.1, 1959, "495.0"),
    ("Bert Blyleven", 96.1, 20491, "4970.0"), ("Phil Niekro", 97.0, 22677, "5404.0"),
    ("Gaylord Perry", 93.0, 21953, "5350.0"), ("Warren Spahn", 92.6, 21547, "5243.2"),
    ("Tom Gordon", 35.0, 9058, "2108.0"), ("Ellis Kinder", 30.9, 6302, "1479.2"),
    ("Bobby Shantz", 32.1, 8045, "1935.2"),
]

# (name, pos WAR, PA, pitch WAR, BF, IP)
TWO_WAY = [
    ("Babe Ruth", 162.3, 10628, 20.4, 4896, "1221.1"),
    ("Walter Johnson", 13.0, 2534, 155.4, 23415, "5914.1"),
    ("Shohei Ohtani", 38.4, 4947, 19.4, 2479, "614.1"),
    ("Bullet Rogan", 20.5, 2326, 37.3, 6063, "1475.2"),
    ("Wes Ferrell", 11.3, 1345, 48.8, 11568, "2623.0"),
    ("Red Ruffing", 13.2, 2084, 55.3, 18546, "4344.0"),
    ("Bob Caruthers", 14.8, 2906, 44.7, 11842, "2828.2"),
    ("John Ward", 34.3, 8114, 28.1, 10164, "2469.2"),
    ("Martin Dihigo", 12.4, 1673, 10.0, 1702, "401.2"),
    ("George Uhle", 10.6, 1514, 45.1, 13597, "3119.2"),
    ("Bob Lemon", 10.7, 1326, 37.5, 12099, "2850.0"),
    ("George Mullin", 12.8, 1694, 34.3, 15169, "3686.2"),
    ("Red Lucas", 12.0, 1606, 32.7, 10651, "2542.0"),
    ("Elmer Smith", 30.1, 5426, 12.5, 5083, "1210.1"),
    ("Smoky Joe Wood", 10.4, 2274, 30.2, 5653, "1434.1"),
    ("Cy Seymour", 31.4, 6233, 10.1, 4407, "1049.1"),
    ("Dave Foutz", 12.8, 4859, 22.7, 8425, "1997.1"),
    ("Ed Rile", 11.8, 1686, 15.2, 3164, "741.1"),
]

# Secondary-coordinate values used in the unified table / text: (name, pos WAR, PA)
PITCHER_BATTING = [
    ("Roger Clemens", 0.6, 213), ("Cy Young", -2.2, 3107), ("Lefty Grove", -6.5, 1580),
    ("Kid Nichols", -0.8, 2265), ("Pete Alexander", 3.0, 1982), ("Pedro Martinez", -2.2, 518),
    ("Mariano Rivera", 0.0, 4), ("Randy Johnson", -2.5, 691), ("Tom Seaver", 3.9, 1552),
    ("Christy Mathewson", 6.6, 1900), ("Clayton Kershaw", 2.8, 847), ("Greg Maddux", 1.8, 1812),
]

# Season checkpoints quoted in the text: (name, label, years, WAR, exposure, kind)
CHECKPOINTS = [
    ("Albert Pujols", "through 2012", (2001, 2012), 91.4, 8103, "bat"),
    ("Albert Pujols", "2013 on", (2013, 2022), 9.9, 4938, "bat"),
    ("Ken Griffey Jr.", "through 2000", (1989, 2000), 76.2, 7319, "bat"),
    ("Dwight Gooden", "1984-85", (1984, 1985), 17.7, 1944, "pitch"),
    ("Dwight Gooden", "1984-88", (1984, 1988), 29.3, 4718, "pitch"),
    ("Dwight Gooden", "1986-98", (1986, 1998), 30.6, 8762, "pitch"),
    ("Dwight Gooden", "1984-98", (1984, 1998), 48.3, 10706, "pitch"),
    ("Dwight Gooden", "career (summed)", (1984, 2000), 48.4, 11705, "pitch"),
    ("Tim Lincecum", "2007-09", (2007, 2009), 17.5, 2451, "pitch"),
    ("Tim Lincecum", "2007-11", (2007, 2011), 24.5, 4248, "pitch"),
    ("Tim Lincecum", "2012-16", (2012, 2016), -4.6, 2872, "pitch"),
    ("Paul Skenes", "through 2026", (2024, 2026), 17.1, 1959, "pitch"),
]
