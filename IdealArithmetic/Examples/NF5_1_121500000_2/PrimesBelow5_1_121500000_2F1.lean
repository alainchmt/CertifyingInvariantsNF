
import IdealArithmetic.Examples.NF5_1_121500000_2.RI5_1_121500000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [15, 16, 25, 13, 28, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 14, 22, 19, 27], [28, 17, 20, 8, 25], [12, 19, 9, 12, 20], [13, 7, 7, 19, 15], [0, 1]]
 g := ![![[17, 0, 9, 10, 4], [24, 12, 19, 6], [17, 1, 1], []], ![[14, 5, 7, 4, 22, 0, 10, 10], [4, 10, 21, 4], [9, 5, 6, 5, 27, 27, 23, 14], [6, 27, 4, 6, 6, 17, 17, 21]], ![[23, 0, 3, 8, 22, 19, 17, 5], [3, 11, 26, 5], [26, 10, 19, 28, 5, 9], [18, 12, 1, 3, 13, 10, 1, 23]], ![[27, 25, 3, 24, 15, 15, 13, 24], [2, 24, 6, 7], [20, 20, 22, 14, 18, 9, 23, 1], [15, 7, 9, 19, 9, 16, 12, 25]], ![[21, 11, 27, 0, 7, 5, 22, 14], [13, 11, 6, 1], [27, 11, 2, 7, 8, 17, 10, 17], [28, 3, 12, 10, 13, 23, 18, 11]]]
 h' := ![![[6, 14, 22, 19, 27], [24, 23, 14, 16, 2], [6, 3, 8, 28, 8], [0, 0, 0, 1], [0, 1]], ![[28, 17, 20, 8, 25], [28, 28, 14, 11, 13], [1, 5, 21, 3, 27], [10, 25, 13, 13, 14], [6, 14, 22, 19, 27]], ![[12, 19, 9, 12, 20], [22, 22, 21, 6, 8], [3, 15, 10, 3, 18], [19, 18, 15, 11], [28, 17, 20, 8, 25]], ![[13, 7, 7, 19, 15], [28, 14, 22, 1, 23], [0, 13, 14, 12, 6], [24, 4, 22, 8, 4], [12, 19, 9, 12, 20]], ![[0, 1], [14, 0, 16, 24, 12], [21, 22, 5, 12, 28], [8, 11, 8, 25, 11], [13, 7, 7, 19, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 0, 8, 27], [], [], []]
 b := ![[], [0, 14, 9, 10, 28], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [15, 16, 25, 13, 28, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11449364894, -27980006780, 14414487236, -14153047132, 8115225324]
  a := ![-17, -13, -9, -20, -34]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![394805686, -964827820, 497051284, -488036108, 279835356]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 20511149 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![74273, -55109, 16825, 54672, 70576]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![74273, -55109, 16825, 54672, 70576]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![20, 2, 12, 18, 1]] where
  M :=![![![74273, -55109, 16825, 54672, 70576], ![164016, -189364, -437, 53238, 116304], ![159714, -428643, -136126, -191820, -29484], ![-177918, 18782, -103192, -243913, -235230], ![-151425, 225402, 28495, 1311, -77825]]]
  hmulB := by decide  
  f := ![![![856189025, -101604337, 56352593, 126602478, 220587280]], ![![379807434, -45071920, 24998141, 56161152, 97853028]], ![![168483456, -19994007, 11089232, 24913218, 43407828]], ![![-177447108, 21057730, -11679202, -26238649, -45717210]], ![![522708889, -62030098, 34403619, 77291625, 134669949]]]
  g := ![![![-43137, -6331, -26777, -39216, 70576], ![-69744, -13612, -45035, -65814, 116304], ![24174, -11925, 7022, 10932, -29484], ![146022, 15782, 87728, 128717, -235230], ![45325, 12292, 31045, 45231, -77825]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 4 2 4 [2, 11, 23, 26, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 3, 30, 4], [17, 18, 10, 1], [14, 9, 22, 26], [0, 1]]
 g := ![![[13, 28, 22, 16], [2, 22, 3, 1], [8, 2, 5, 1], []], ![[1, 7, 15, 13, 25, 8], [1, 5, 25, 3, 6, 10], [0, 12, 11, 1, 21, 5], [2, 14, 30, 13, 24, 2]], ![[17, 23, 1, 14, 16, 9], [15, 11, 8, 29, 29, 2], [13, 14, 22, 20, 22, 8], [9, 22, 1, 10, 4, 1]], ![[2, 0, 16, 3, 16, 3], [20, 29, 12, 2, 21, 22], [14, 14, 18, 17, 7, 24], [23, 0, 26, 20, 2, 30]]]
 h' := ![![[5, 3, 30, 4], [27, 4, 15, 27], [15, 1, 1, 30], [0, 0, 0, 1], [0, 1]], ![[17, 18, 10, 1], [17, 5, 9, 8], [14, 23, 6, 24], [28, 20, 17, 3], [5, 3, 30, 4]], ![[14, 9, 22, 26], [30, 8, 6, 3], [3, 14, 2, 23], [28, 25, 5, 15], [17, 18, 10, 1]], ![[0, 1], [7, 14, 1, 24], [17, 24, 22, 16], [1, 17, 9, 12], [14, 9, 22, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [15, 19, 14], []]
 b := ![[], [], [22, 8, 5, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 4
  hpos := by decide
  P := [2, 11, 23, 26, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![56228460357, 78835171999, 32559606060, 35943374215, 152200593941]
  a := ![-101, -111, -50, -167, -205]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-96380110273, -7276323093, -57866049072, -87215074733, 152200593941]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 923521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![856189025, -101604337, 56352593, 126602478, 220587280]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![856189025, -101604337, 56352593, 126602478, 220587280]] 
 ![![31, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![856189025, -101604337, 56352593, 126602478, 220587280], ![379807434, -45071920, 24998141, 56161152, 97853028], ![168483456, -19994007, 11089232, 24913218, 43407828], ![-177447108, 21057730, -11679202, -26238649, -45717210], ![-507173337, 60186486, -33381101, -74994423, -130667393]]]
  hmulB := by decide  
  f := ![![![74273, -55109, 16825, 54672, 70576]], ![![50813, -39885, 10298, 35226, 47008]], ![![31507, -33382, 1579, 13212, 24092]], ![![61346, -49170, 11868, 41513, 56158]], ![![52617, -35394, 13945, 42369, 52129]]]
  g := ![![![-215231329, -101604337, 56352593, 126602478, 220587280], ![-95477115, -45071920, 24998141, 56161152, 97853028], ![-42353869, -19994007, 11089232, 24913218, 43407828], ![44607176, 21057730, -11679202, -26238649, -45717210], ![127494736, 60186486, -33381101, -74994423, -130667393]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![74273, -55109, 16825, 54672, 70576]] ![![856189025, -101604337, 56352593, 126602478, 220587280]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-623, -430, -772, -1624, -1062]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-623, -430, -772, -1624, -1062]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![17, 33, 24, 1, 0], ![28, 33, 22, 0, 1]] where
  M :=![![![-623, -430, -772, -1624, -1062], ![-4872, 185, -2054, -6318, -6558], ![-18954, 15678, -6133, -11604, -18234], ![-3366, 8048, 1706, 341, 792], ![6948, -6870, 2638, 6162, 5305]]]
  hmulB := by decide  
  f := ![![![-657617420075, 78039755418, -43283020164, -97240203376, -169427583918]], ![![-291720610128, 34618616189, -19200447958, -43135979358, -75158468502]], ![![-129407938074, 15356898294, -8517363169, -19135220316, -33340470642]], ![![-642588489037, 76256265403, -42293846968, -95017913841, -165555552252]], ![![-824256631148, 97814905647, -54250868814, -121880716660, -212360264921]]]
  g := ![![![1533, 2384, 1664, -1624, -1062], ![7734, 11489, 7942, -6318, -6558], ![18618, 27036, 18203, -11604, -18234], ![-847, -793, -646, 341, 792], ![-6658, -10413, -7080, 6162, 5305]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [21, 28, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 27, 20], [3, 9, 17], [0, 1]]
 g := ![![[32, 13, 10], [], [11, 1, 28], [34, 1], []], ![[4, 13, 34, 8], [12, 34], [35, 11, 27, 14], [34, 7], [28, 30]], ![[34, 6, 4, 8], [8, 34], [13, 23, 9, 5], [16, 26], [31, 30]]]
 h' := ![![[31, 27, 20], [7, 7, 11], [28, 14], [26, 26, 18], [0, 0, 1], [0, 1]], ![[3, 9, 17], [35, 15, 17], [18, 8, 21], [35, 17, 16], [3, 1, 9], [31, 27, 20]], ![[0, 1], [33, 15, 9], [33, 15, 16], [18, 31, 3], [24, 36, 27], [3, 9, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 23], []]
 b := ![[], [29, 21, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [21, 28, 3, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![22884, -14348, 12055, -2257, 32632]
  a := ![-6, -7, -3, -11, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-23039, -27479, -17613, -2257, 32632]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![657617420075, -78039755418, 43283020164, 97240203376, 169427583918]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![657617420075, -78039755418, 43283020164, 97240203376, 169427583918]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![6, 4, 1, 0, 0], ![33, 5, 0, 1, 0], ![15, 24, 0, 0, 1]] where
  M :=![![![657617420075, -78039755418, 43283020164, 97240203376, 169427583918], ![291720610128, -34618616189, 19200447958, 43135979358, 75158468502], ![129407938074, -15356898294, 8517363169, 19135220316, 33340470642], ![-136292694906, 16173915488, -8970503642, -20153251673, -35114249256], ![-389547181476, 46227739470, -25639190806, -57601343874, -100362362317]]]
  hmulB := by decide  
  f := ![![![623, 430, 772, 1624, 1062]], ![![4872, -185, 2054, 6318, 6558]], ![![1140, -374, 513, 1260, 1374]], ![![1305, 141, 920, 2293, 1812]], ![![3225, 240, 1574, 4590, 4541]]]
  g := ![![![-144660031651, -129827969378, 43283020164, 97240203376, 169427583918], ![-64171524972, -57591987807, 19200447958, 43135979358, 75158468502], ![-28466637054, -25547939134, 8517363169, 19135220316, 33340470642], ![29981118135, 26907139745, -8970503642, -20153251673, -35114249256], ![85691020161, 76905078856, -25639190806, -57601343874, -100362362317]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P1 : CertificateIrreducibleZModOfList' 37 2 2 5 [19, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 36], [0, 1]]
 g := ![![[15, 21], [36], [33, 33], [10], [1]], ![[24, 16], [36], [26, 4], [10], [1]]]
 h' := ![![[11, 36], [23, 13], [2, 6], [23, 25], [18, 11], [0, 1]], ![[0, 1], [18, 24], [31, 31], [2, 12], [28, 26], [11, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [6, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N1 : CertifiedPrimeIdeal' SI37N1 37 where
  n := 2
  hpos := by decide
  P := [19, 26, 1]
  hirr := P37P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4506, -71667, 2761, -27592, -35643]
  a := ![65, 55, 33, 82, 129]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![38733, 24613, 2761, -27592, -35643]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N1 B_one_repr
lemma NI37N1 : Nat.card (O ⧸ I37N1) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-623, -430, -772, -1624, -1062]] ![![657617420075, -78039755418, 43283020164, 97240203376, 169427583918]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![88990109486, -10560496380, 5857145181, 13158739537, 22927280794]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![88990109486, -10560496380, 5857145181, 13158739537, 22927280794]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![16, 14, 34, 1, 0], ![2, 29, 39, 0, 1]] where
  M :=![![![88990109486, -10560496380, 5857145181, 13158739537, 22927280794], ![39476218611, -4684660661, 2598243157, 5837247315, 10170594840], ![17511741945, -2078126328, 1152586654, 2589416367, 4511699370], ![-18443401122, 2188686734, -1213906572, -2727178505, -4751730738], ![-52714306629, 6255630528, -3469546761, -7794729471, -13581236339]]]
  hmulB := by decide  
  f := ![![![-1904, -165202, 16321, -49879, -104056]], ![![-149637, 571637, -215081, 260457, 12894]], ![![781371, -351330, 832094, -547797, 1524060]], ![![591272, -195896, 621924, -392947, 1195546]], ![![633739, 106573, 631616, -323545, 1472685]]]
  g := ![![![-4083031334, -20967658364, -32578145123, 13158739537, 22927280794], ![-1811242149, -9301301791, -14451740593, 5837247315, 10170594840], ![-803471187, -4126078956, -6410825494, 2589416367, 4511699370], ![846217474, 4345594566, 6751894180, -2727178505, -4751730738], ![2418630185, 12420431633, 19298035914, -7794729471, -13581236339]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [35, 35, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 19, 17], [35, 21, 24], [0, 1]]
 g := ![![[14, 2, 18], [35, 40], [15, 2], [22, 37, 1], []], ![[21, 3, 2, 19], [16, 39], [9, 31], [12, 19, 27, 35], [23, 2]], ![[33, 11], [17, 31], [13, 16], [0, 26, 21, 13], [16, 2]]]
 h' := ![![[2, 19, 17], [13, 25, 31], [7, 37, 32], [9, 26, 17], [0, 0, 1], [0, 1]], ![[35, 21, 24], [37, 19, 10], [33, 22, 30], [15, 31, 20], [19, 21, 21], [2, 19, 17]], ![[0, 1], [19, 38], [32, 23, 20], [6, 25, 4], [9, 20, 19], [35, 21, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 5], []]
 b := ![[], [34, 9, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [35, 35, 4, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-239383, -9437750, 676106, -2861350, -6246088]
  a := ![-33, -20, -16, -29, -65]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1415473, 5164822, 8330718, -2861350, -6246088]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1904, 165202, -16321, 49879, 104056]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![1904, 165202, -16321, 49879, 104056]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![2, 1, 1, 0, 0], ![27, 28, 0, 1, 0], ![32, 27, 0, 0, 1]] where
  M :=![![![1904, 165202, -16321, 49879, 104056], ![149637, -571637, 215081, -260457, -12894], ![-781371, 351330, -832094, 547797, -1524060], ![199080, 1446202, 42314, 334063, 1316274], ![146889, -1824294, 350703, -645243, -775931]]]
  hmulB := by decide  
  f := ![![![-88990109486, 10560496380, -5857145181, -13158739537, -22927280794]], ![![-39476218611, 4684660661, -2598243157, -5837247315, -10170594840]], ![![-5730931208, 680092189, -377198053, -847418116, -1476508678]], ![![-85112772588, 10100371074, -5601946871, -12585407654, -21928329420]], ![![-94166514620, 11174782719, -6197845470, -13924161298, -24260922189]]]
  g := ![![![-113219, -98161, -16321, 49879, 104056], ![174742, 167176, 215081, -260457, -12894], ![850298, 658408, -832094, 547797, -1524060], ![-1244537, -1060714, 42314, 334063, 1316274], ![1016996, 898584, 350703, -645243, -775931]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [23, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 40], [0, 1]]
 g := ![![[2, 25], [31], [9], [23, 25], [1]], ![[0, 16], [31], [9], [21, 16], [1]]]
 h' := ![![[36, 40], [16, 36], [14, 20], [4, 3], [18, 36], [0, 1]], ![[0, 1], [0, 5], [37, 21], [30, 38], [2, 5], [36, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [27, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [23, 5, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4639, -2398, -4386, 2062, -11844]
  a := ![18, 2, 10, -2, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7987, 6440, -4386, 2062, -11844]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![88990109486, -10560496380, 5857145181, 13158739537, 22927280794]] ![![1904, 165202, -16321, 49879, 104056]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![-41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![48143556942410, -5713217585247, 3168709468900, 7118864442171, 12403635130348]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![48143556942410, -5713217585247, 3168709468900, 7118864442171, 12403635130348]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![2, 31, 1, 0, 0], ![4, 27, 0, 1, 0], ![25, 22, 0, 0, 1]] where
  M :=![![![48143556942410, -5713217585247, 3168709468900, 7118864442171, 12403635130348], ![21356593326513, -2534396548636, 1405646856924, 3157944748869, 5502281261982], ![9473834246607, -1124264176869, 623548200233, 1400871602205, 2440824707268], ![-9977860862154, 1184077242336, -656722190906, -1475400726733, -2570681382420], ![-28518385220100, 3384289618176, -1877021205410, -4216940570772, -7347434781359]]]
  hmulB := by decide  
  f := ![![![1283642, 917619, 1201806, -438921, 3406978]], ![![-1316763, -16430650, 478698, -4326861, -12854460]], ![![-1191464, -10207501, -81727, -2478036, -8815630]], ![![-361213, -10404678, 782960, -3005782, -7089800]], ![![-178930, -8439865, 750916, -2502327, -5497477]]]
  g := ![![![-6901399954018, -13233314509940, 3168709468900, 7118864442171, 12403635130348], ![-3061476998427, -5870328955729, 1405646856924, 3157944748869, 5502281261982], ![-1358078284753, -2604091516361, 623548200233, 1400871602205, 2440824707268], ![1430330720630, 2742634306871, -656722190906, -1475400726733, -2570681382420], ![4088123000181, 7838904827596, -1877021205410, -4216940570772, -7347434781359]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [34, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 42], [0, 1]]
 g := ![![[16, 6], [4, 9], [11], [33, 10], [1]], ![[20, 37], [10, 34], [11], [11, 33], [1]]]
 h' := ![![[15, 42], [36, 36], [29, 40], [39, 21], [9, 15], [0, 1]], ![[0, 1], [17, 7], [27, 3], [10, 22], [19, 28], [15, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [5, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [34, 28, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1071, -37355, -1318, -10558, -23443]
  a := ![55, 37, 28, 56, 97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14698, 18705, -1318, -10558, -23443]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-32, 246, 17, 11, 132]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-32, 246, 17, 11, 132]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![36, 2, 1, 0, 0], ![31, 13, 0, 1, 0], ![30, 23, 0, 0, 1]] where
  M :=![![![-32, 246, 17, 11, 132], ![33, -751, 257, -261, -330], ![-783, 2262, -1012, 1749, -576], ![858, 898, 540, 281, 2202], ![-153, -2394, 1, -771, -1781]]]
  hmulB := by decide  
  f := ![![![-14838172286, 1760852588, -976617849, -2194082527, -3822884862]], ![![-6582247581, 781118285, -433229939, -973300089, -1695840576]], ![![-12796711575, 1518591526, -842253122, -1892216961, -3296925930]], ![![-12615751505, 1497116913, -830342704, -1865458859, -3250303644]], ![![-13668541914, 1622052025, -899635194, -2021132280, -3521543015]]]
  g := ![![![-115, -69, 17, 11, 132], ![204, 226, 257, -261, -330], ![-30, -121, -1012, 1749, -576], ![-2171, -1267, 540, 281, 2202], ![1794, 1130, 1, -771, -1781]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [35, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 42], [0, 1]]
 g := ![![[0, 16], [], [11], [], [1]], ![[0, 27], [], [11], [], [1]]]
 h' := ![![[0, 42], [0, 4], [2], [0, 21], [8], [0, 1]], ![[0, 1], [0, 39], [2], [0, 22], [8], [0, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [0, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [35, 0, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![164, 51, -25, 56, 227]
  a := ![-3, -5, -1, -8, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-174, -136, -25, 56, 227]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-673, 595, -749, 562, -1136]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-673, 595, -749, 562, -1136]] 
 ![![43, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![41, 0, 0, 0, 1]] where
  M :=![![![-673, 595, -749, 562, -1136], ![1686, 5020, 1157, 600, 6780], ![1800, -34323, 5620, -11598, -16740], ![-6642, 13474, -8232, 7891, -6618], ![6741, 1038, 6729, -3471, 15607]]]
  hmulB := by decide  
  f := ![![![-179497, 21603, -11621, -26180, -46016]], ![![-43570, 5242, -2809, -6326, -11144]], ![![-121769, 14604, -7857, -17680, -31132]], ![![-15796, 1862, -1026, -2299, -4034]], ![![-168716, 20319, -10936, -24643, -43287]]]
  g := ![![![1382, 595, -749, 562, -1136], ![-8429, 5020, 1157, 600, 6780], ![21274, -34323, 5620, -11598, -16740], ![7840, 13474, -8232, 7891, -6618], ![-19181, 1038, 6729, -3471, 15607]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![48143556942410, -5713217585247, 3168709468900, 7118864442171, 12403635130348]] ![![-32, 246, 17, 11, 132]]
  ![![-179497, 21603, -11621, -26180, -46016]] where
 M := ![![![-179497, 21603, -11621, -26180, -46016]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-179497, 21603, -11621, -26180, -46016]] ![![-673, 595, -749, 562, -1136]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 5 2 5 [29, 34, 25, 16, 40, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 14, 25, 32, 16], [12, 38, 31, 14, 39], [13, 27, 7, 14, 1], [40, 14, 31, 34, 38], [0, 1]]
 g := ![![[2, 38, 32, 33, 42], [39, 22, 17, 46, 24], [33, 29, 2, 25, 2], [1], []], ![[43, 11, 9, 40, 28, 40, 14, 16], [2, 18, 5, 4, 24, 43, 33, 34], [13, 36, 1, 44, 19, 7, 12, 6], [14, 36, 13, 21, 12, 39, 39, 25], [10, 3, 43, 21]], ![[7, 35, 37, 0, 36, 16, 13, 43], [44, 18, 17, 1, 32, 39, 0, 26], [36, 32, 12, 21, 0, 12, 43, 20], [25, 41, 32, 30, 33, 1, 7, 45], [27, 9, 36, 17]], ![[29, 8, 30, 45, 2, 42, 3, 25], [8, 8, 11, 7, 18, 37, 22, 12], [42, 22, 24, 28, 42, 6, 29, 8], [11, 27, 30, 3, 24, 45, 41, 37], [12, 16, 35, 1]], ![[2, 44, 30, 29, 41, 44, 41, 10], [29, 37, 18, 31, 9, 11, 44, 11], [25, 41, 16, 9, 30, 8, 0, 13], [20, 14, 27, 35, 8, 16, 43, 15], [40, 21, 2, 34]]]
 h' := ![![[36, 14, 25, 32, 16], [44, 17, 24, 28, 18], [30, 6, 9, 43, 27], [18, 13, 22, 31, 7], [0, 0, 1], [0, 1]], ![[12, 38, 31, 14, 39], [26, 45, 33, 7, 46], [26, 5, 37, 6, 14], [41, 0, 25, 3, 26], [19, 17, 21, 40, 13], [36, 14, 25, 32, 16]], ![[13, 27, 7, 14, 1], [21, 12, 4, 9, 20], [26, 24, 11, 44, 28], [35, 1, 7, 6, 31], [19, 15, 22, 36, 24], [12, 38, 31, 14, 39]], ![[40, 14, 31, 34, 38], [13, 32, 21, 23, 5], [33, 11, 10, 42, 23], [29, 25, 4, 10, 33], [9, 18, 39, 12, 32], [13, 27, 7, 14, 1]], ![[0, 1], [28, 35, 12, 27, 5], [15, 1, 27, 6, 2], [29, 8, 36, 44, 44], [17, 44, 11, 6, 25], [40, 14, 31, 34, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 41, 41, 43], [], [], []]
 b := ![[], [2, 22, 22, 4, 12], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 5
  hpos := by decide
  P := [29, 34, 25, 16, 40, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![372147838499, 3552188604086, -14602743678, 880325736916, 2975521077042]
  a := ![39, 22, 23, 31, 75]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7918039117, 75578480938, -310696674, 18730334828, 63308959086]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 229345007 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]] where
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 5 2 5 [7, 37, 51, 32, 44, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 24, 2, 12, 31], [1, 46, 0, 33, 36], [13, 41, 3, 34, 10], [6, 47, 48, 27, 29], [0, 1]]
 g := ![![[47, 50, 34, 43, 52], [28, 46, 9, 46], [40, 10, 27, 47, 16], [9, 1], []], ![[28, 3, 51, 37, 49, 29, 27, 26], [20, 12, 30, 17], [36, 7, 25, 9, 49, 31, 34, 45], [46, 11, 3, 36], [2, 12, 39, 38, 10, 47, 32, 5]], ![[20, 47, 30, 36, 13, 16, 2, 13], [6, 36], [40, 40, 30, 45, 17, 2, 1, 49], [38, 8, 33, 36], [25, 34, 15, 10, 46, 19, 29, 16]], ![[24, 52, 42, 4, 18, 14, 18, 1], [39, 9, 18, 49], [47, 29, 5, 22, 10, 13, 26, 16], [39, 0, 27, 11], [44, 9, 6, 29, 39, 49, 14, 46]], ![[28, 33, 22, 52, 21, 27, 16, 43], [6, 8, 22, 47], [43, 34, 6, 36, 42, 13, 33, 7], [49, 20, 42, 29], [34, 3, 46, 2, 23, 36, 44, 9]]]
 h' := ![![[42, 24, 2, 12, 31], [29, 7, 34, 15, 30], [38, 34, 14, 25, 29], [43, 31, 34, 32, 49], [0, 0, 0, 1], [0, 1]], ![[1, 46, 0, 33, 36], [8, 13, 46, 25, 10], [28, 14, 31, 16, 21], [25, 31, 44, 18, 13], [33, 21, 32, 13, 6], [42, 24, 2, 12, 31]], ![[13, 41, 3, 34, 10], [10, 11, 42, 50, 24], [23, 14, 0, 6], [12, 32, 32, 42, 43], [38, 35, 0, 42, 6], [1, 46, 0, 33, 36]], ![[6, 47, 48, 27, 29], [29, 35, 15, 10, 49], [14, 38, 8, 34, 46], [35, 16, 22, 12, 37], [34, 16, 13, 22, 8], [13, 41, 3, 34, 10]], ![[0, 1], [11, 40, 22, 6, 46], [0, 6, 0, 25, 10], [35, 49, 27, 2, 17], [31, 34, 8, 28, 33], [6, 47, 48, 27, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 6, 44, 33], [], [], []]
 b := ![[], [11, 29, 34, 11, 28], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 5
  hpos := by decide
  P := [7, 37, 51, 32, 44, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-48204716986, 184381856827, -69060946531, 83307514276, 4611728379]
  a := ![23, 15, 11, 22, 45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-909522962, 3478902959, -1303036727, 1571839892, 87013743]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 418195493 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7882, 4456, -2573, -7185, -8310]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-7882, 4456, -2573, -7185, -8310]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![21, 56, 1, 0, 0], ![40, 32, 0, 1, 0], ![42, 37, 0, 0, 1]] where
  M :=![![![-7882, 4456, -2573, -7185, -8310], ![-21555, 19889, -2729, -12063, -18180], ![-36189, 55212, 7826, 1977, -17838], ![11766, 6434, 10896, 23765, 19986], ![23157, -25932, 477, 8187, 16967]]]
  hmulB := by decide  
  f := ![![![-1523914201244, 180843584602, -100300884811, -225337289331, -392619011196]], ![![-676011867993, 80222632837, -44493704729, -99960143271, -174166702398]], ![![-1189131241755, 141114740020, -78266161971, -175833790680, -306366022404]], ![![-1394459545204, 165481142266, -91780446762, -206195160949, -359266504206]], ![![-1493459789910, 177229545893, -98296438366, -220834073538, -384772781497]]]
  g := ![![![11569, 11626, -2573, -7185, -8310], ![21726, 20871, -2729, -12063, -18180], ![7959, 3622, 7826, 1977, -17838], ![-34018, -35656, 10896, 23765, 19986], ![-17406, -15973, 477, 8187, 16967]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [12, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 58], [0, 1]]
 g := ![![[36, 5], [7, 19], [26], [18, 25], [40, 1]], ![[0, 54], [0, 40], [26], [15, 34], [21, 58]]]
 h' := ![![[40, 58], [34, 8], [29, 45], [20, 12], [51, 54], [0, 1]], ![[0, 1], [0, 51], [0, 14], [28, 47], [28, 5], [40, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [35, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [12, 19, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![435, -5815, 180, -1913, -2996]
  a := ![21, 15, 10, 23, 38]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3373, 2647, 180, -1913, -2996]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![226579, -26889, 14913, 33504, 58376]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![226579, -26889, 14913, 33504, 58376]] 
 ![![59, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![38, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![43, 0, 0, 0, 1]] where
  M :=![![![226579, -26889, 14913, 33504, 58376], ![100512, -11930, 6615, 14862, 25896], ![44586, -5295, 2932, 6588, 11484], ![-46962, 5574, -3092, -6947, -12102], ![-134217, 15930, -8833, -19845, -34579]]]
  hmulB := by decide  
  f := ![![![-361, -309, -335, 114, -992]], ![![-190, -86, -185, 84, -476]], ![![-166, -531, -112, -66, -692]], ![![-299, -165, -287, 121, -766]], ![![-212, -99, -206, 93, -533]]]
  g := ![![![-54737, -26889, 14913, 33504, 58376], ![-24280, -11930, 6615, 14862, 25896], ![-10762, -5295, 2932, 6588, 11484], ![11349, 5574, -3092, -6947, -12102], ![32421, 15930, -8833, -19845, -34579]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, -318, 6, -82, -256]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-29, -318, 6, -82, -256]] 
 ![![59, 0, 0, 0, 0], ![43, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![53, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![-29, -318, 6, -82, -256], ![-246, 1361, -400, 558, 276], ![1674, -1986, 1919, -1554, 2520], ![-654, -2480, -390, -397, -2952], ![-54, 3792, -474, 1200, 2171]]]
  hmulB := by decide  
  f := ![![![1181, -2630, -550, -506, 424]], ![![835, -1985, -454, -472, 236]], ![![471, -1692, -535, -744, -120]], ![![869, -2202, -528, -579, 208]], ![![204, -228, 18, 108, 179]]]
  g := ![![![327, -318, 6, -82, -256], ![-1261, 1361, -400, 558, 276], ![1347, -1986, 1919, -1554, 2520], ![2711, -2480, -390, -397, -2952], ![-3750, 3792, -474, 1200, 2171]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2

def I59N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35237812, -4181687, 2319280, 5210525, 9078618]] i)))

def SI59N3: IdealEqSpanCertificate' Table ![![35237812, -4181687, 2319280, 5210525, 9078618]] 
 ![![59, 0, 0, 0, 0], ![46, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![35237812, -4181687, 2319280, 5210525, 9078618], ![15631575, -1855006, 1028838, 2311401, 4027296], ![6934203, -822885, 456395, 1025343, 1786518], ![-7303116, 866664, -480676, -1079893, -1881564], ![-20873520, 2477070, -1373852, -3086514, -5377823]]]
  hmulB := by decide  
  f := ![![![-208, -109, -170, -95, -456]], ![![-167, -54, -136, -73, -342]], ![![-25, -109, 9, -71, -96]], ![![-76, -10, -64, -3, -156]], ![![-34, 5, -34, -17, -59]]]
  g := ![![![-309198, -4181687, 2319280, 5210525, 9078618], ![-137161, -1855006, 1028838, 2311401, 4027296], ![-60845, -822885, 456395, 1025343, 1786518], ![64082, 866664, -480676, -1079893, -1881564], ![183157, 2477070, -1373852, -3086514, -5377823]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N3 : Nat.card (O ⧸ I59N3) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N3)

lemma isPrimeI59N3 : Ideal.IsPrime I59N3 := prime_ideal_of_norm_prime hp59.out _ NI59N3
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-7882, 4456, -2573, -7185, -8310]] ![![226579, -26889, 14913, 33504, 58376]]
  ![![31256, -24437, 6388, 21765, 28972]] where
 M := ![![![31256, -24437, 6388, 21765, 28972]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![31256, -24437, 6388, 21765, 28972]] ![![-29, -318, 6, -82, -256]]
  ![![-208, -109, -170, -95, -456]] where
 M := ![![![-208, -109, -170, -95, -456]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N2 : IdealMulLeCertificate' Table 
  ![![-208, -109, -170, -95, -456]] ![![35237812, -4181687, 2319280, 5210525, 9078618]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2, I59N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
    exact isPrimeI59N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1 ⊙ MulI59N2)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-655570169, 77796813, -43148267, -96937486, -168900114]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-655570169, 77796813, -43148267, -96937486, -168900114]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![9, 47, 5, 40, 1]] where
  M :=![![![-655570169, 77796813, -43148267, -96937486, -168900114], ![-290812458, 34510742, -19140673, -43001718, -74924574], ![-129005154, 15309531, -8490976, -19075470, -33236586], ![135868494, -16123622, 8942680, 20090441, 35005110], ![388334403, -46083972, 25559317, 57422019, 100049677]]]
  hmulB := by decide  
  f := ![![![3733, -16981, -7049, -11428, -4758]], ![![-34284, -11722, -28409, -62304, -54294]], ![![-186912, 81645, -74026, -194484, -210942]], ![![-80100, 83810, -4602, -34645, -61866]], ![![-92670, 49974, -31427, -86953, -99035]]]
  g := ![![![14172637, 131411511, 13136923, 109165034, -168900114], ![6287028, 58294520, 5827577, 48425922, -74924574], ![2788920, 25859493, 2585114, 21481770, -33236586], ![-2937336, -27235472, -2722670, -22624819, 35005110], ![-8395290, -77842931, -7781788, -64665001, 100049677]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 4 2 5 [20, 1, 57, 6, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 29, 59, 32], [9, 55, 38, 58], [33, 37, 25, 32], [0, 1]]
 g := ![![[39, 60, 55, 52], [22, 44, 45], [16, 15, 13, 52], [40, 40, 55, 1], []], ![[5, 31, 17, 47, 53, 8], [43, 38, 9], [44, 46, 45, 2, 32, 31], [8, 28, 25, 56, 57, 18], [58, 47, 51, 18, 12, 11]], ![[33, 56, 10, 47, 32, 49], [0, 14, 46], [7, 1, 24, 32, 10, 12], [60, 40, 9, 36, 35, 57], [21, 3, 7, 41, 29, 34]], ![[7, 23, 56, 34, 11, 7], [42, 17, 45], [34, 50, 25, 26, 8, 33], [59, 10, 26, 1, 51, 11], [6, 6, 42, 4, 57, 11]]]
 h' := ![![[13, 29, 59, 32], [29, 32, 49, 33], [46, 38, 20, 17], [54, 14, 57, 28], [0, 0, 0, 1], [0, 1]], ![[9, 55, 38, 58], [50, 2, 27, 31], [19, 26, 5, 58], [23, 42, 7, 23], [0, 41, 23, 16], [13, 29, 59, 32]], ![[33, 37, 25, 32], [4, 6, 16, 2], [59, 20, 15, 30], [42, 49, 1, 22], [4, 47, 21, 15], [9, 55, 38, 58]], ![[0, 1], [19, 21, 30, 56], [35, 38, 21, 17], [46, 17, 57, 49], [10, 34, 17, 29], [33, 37, 25, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [60, 12, 58], []]
 b := ![[], [], [43, 34, 26, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 4
  hpos := by decide
  P := [20, 1, 57, 6, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-912357431, 1277518586, -1045250094, 935331633, -1257989683]
  a := ![-23, -14, -24, -21, -53]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![170648356, 990213667, 85978661, 840244573, -1257989683]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 13845841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3733, -16981, -7049, -11428, -4758]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![3733, -16981, -7049, -11428, -4758]] 
 ![![61, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![3733, -16981, -7049, -11428, -4758], ![-34284, -11722, -28409, -62304, -54294], ![-186912, 81645, -74026, -194484, -210942], ![-80100, 83810, -4602, -34645, -61866], ![63441, -8448, 35827, 85227, 82855]]]
  hmulB := by decide  
  f := ![![![-655570169, 77796813, -43148267, -96937486, -168900114]], ![![-79996781, 9493253, -5265222, -11828920, -20610252]], ![![-131079462, 15555267, -8627380, -19382382, -33771114]], ![![-137484323, 16315327, -9048931, -20329457, -35421252]], ![![-47369122, 5621313, -3117738, -7004351, -12204113]]]
  g := ![![![6222, -16981, -7049, -11428, -4758], ![24100, -11722, -28409, -62304, -54294], ![60867, 81645, -74026, -194484, -210942], ![2429, 83810, -4602, -34645, -61866], ![-29993, -8448, 35827, 85227, 82855]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-655570169, 77796813, -43148267, -96937486, -168900114]] ![![3733, -16981, -7049, -11428, -4758]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![61, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)


lemma PB687I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB687I1 : PrimesBelowBoundCertificateInterval O 23 61 687 where
  m := 9
  g := ![1, 2, 2, 2, 3, 1, 1, 4, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB687I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0, I59N1, I59N2, I59N3]
    · exact ![I61N0, I61N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![20511149]
    · exact ![923521, 31]
    · exact ![50653, 1369]
    · exact ![68921, 1681]
    · exact ![1849, 1849, 43]
    · exact ![229345007]
    · exact ![418195493]
    · exact ![3481, 59, 59, 59]
    · exact ![13845841, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
      exact NI59N3
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
  β := ![I31N1, I43N2, I59N1, I59N2, I59N3, I61N1]
  Il := ![[], [I31N1], [], [], [I43N2], [], [], [I59N1, I59N2, I59N3], [I61N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
