
import IdealArithmetic.Examples.NF5_1_75000000_1.RI5_1_75000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47659, -22164, 12158, -13047, -45411]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-47659, -22164, 12158, -13047, -45411]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![25, 7, 12, 1, 1]] where
  M :=![![![-47659, -22164, 12158, -13047, -45411], ![168090, 63369, -53639, 42237, 108618], ![-313812, -61888, 141152, -64401, -6111], ![-208088, -166517, 2388, -74795, -441239], ![161544, 117121, -10685, 54966, 300248]]]
  hmulB := by decide  
  f := ![![![9812041, -962822, -958503, 1222350, 3609168]], ![![-11876208, 1165390, 1160149, -1479513, -4368462]], ![![14374668, -1410484, -1404195, 1790703, 5287359]], ![![-4966690, 487465, 485206, -618814, -1827055]], ![![11395557, -1118178, -1113183, 1419595, 4191588]]]
  g := ![![![37504, 10197, 19210, 1116, -45411], ![-87840, -24033, -46795, -2289, 108618], ![-5553, -659, 7396, -2010, -6111], ![373203, 100764, 182664, 12636, -441239], ![-253264, -68435, -124609, -8458, 300248]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 4 2 4 [22, 5, 6, 7, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 26, 5, 10], [21, 27, 5, 8], [18, 4, 19, 11], [0, 1]]
 g := ![![[10, 20, 4, 25], [2, 24, 6], [26, 14, 22, 1], []], ![[0, 9, 27, 4, 25, 17], [8, 20, 20], [0, 9, 20, 9, 27, 21], [20, 2, 9, 15, 10, 14]], ![[17, 5, 10, 15, 1, 21], [16, 21, 28], [8, 18, 4, 1, 27, 26], [2, 17, 4, 26, 15, 19]], ![[15, 8, 26, 11, 25, 17], [6, 3, 9], [11, 24, 23, 2, 19, 10], [11, 4, 19, 18, 16, 26]]]
 h' := ![![[12, 26, 5, 10], [20, 23, 14, 24], [8, 26, 15, 8], [0, 0, 0, 1], [0, 1]], ![[21, 27, 5, 8], [26, 11, 15, 15], [17, 17, 28, 7], [12, 10, 10, 18], [12, 26, 5, 10]], ![[18, 4, 19, 11], [26, 16, 23, 12], [1, 18, 26, 17], [24, 15, 12, 24], [21, 27, 5, 8]], ![[0, 1], [17, 8, 6, 7], [2, 26, 18, 26], [22, 4, 7, 15], [18, 4, 19, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [16, 10, 16], []]
 b := ![[], [], [4, 7, 15, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 4
  hpos := by decide
  P := [22, 5, 6, 7, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13580496300, -28412718339, -9611986879, 18008336537, 30258687898]
  a := ![-72, -11, 19, -85, -207]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-26553368750, -8283570125, -12852284195, -422425909, 30258687898]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 707281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9812041, -962822, -958503, 1222350, 3609168]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![9812041, -962822, -958503, 1222350, 3609168]] 
 ![![29, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![9812041, -962822, -958503, 1222350, 3609168], ![-11876208, 1165390, 1160149, -1479513, -4368462], ![14374668, -1410484, -1404195, 1790703, 5287359], ![-4966690, 487465, 485206, -618814, -1827055], ![774258, -75999, -75641, 96474, 284833]]]
  hmulB := by decide  
  f := ![![![-47659, -22164, 12158, -13047, -45411]], ![![-18855, -9279, 4439, -5292, -19743]], ![![-22325, -7484, 7802, -5370, -11172]], ![![-25253, -14149, 4694, -7528, -32440]], ![![-4290, -547, 2147, -804, 958]]]
  g := ![![![-142654, -962822, -958503, 1222350, 3609168], ![172666, 1165390, 1160149, -1479513, -4368462], ![-208986, -1410484, -1404195, 1790703, 5287359], ![72213, 487465, 485206, -618814, -1827055], ![-11258, -75999, -75641, 96474, 284833]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-47659, -22164, 12158, -13047, -45411]] ![![9812041, -962822, -958503, 1222350, 3609168]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -2, 1, 3, 10]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-5, -2, 1, 3, 10]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![15, 6, 28, 22, 1]] where
  M :=![![![-5, -2, 1, 3, 10], ![-36, -33, 1, 3, -21], ![150, 29, -61, 96, 258], ![-222, -157, 32, 34, 41], ![114, 58, -29, 6, 20]]]
  hmulB := by decide  
  f := ![![![-17, 3, 2, -3, -8]], ![![24, 2, -1, 0, 3]], ![![-18, 16, 6, -12, -27]], ![![24, 21, 4, -11, -19]], ![![-3, 31, 9, -20, -41]]]
  g := ![![![-5, -2, -9, -7, 10], ![9, 3, 19, 15, -21], ![-120, -49, -235, -180, 258], ![-27, -13, -36, -28, 41], ![-6, -2, -19, -14, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 4 2 4 [15, 19, 17, 4, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 26, 11, 2], [29, 23, 24, 3], [27, 12, 27, 26], [0, 1]]
 g := ![![[4, 14, 9, 20], [16, 23, 13, 7], [22, 30, 27, 1], []], ![[30, 10, 18, 5, 25, 14], [1, 14, 16, 3, 26, 14], [26, 1, 5, 8, 2, 14], [24, 23, 28, 6, 7, 8]], ![[6, 8, 5, 5, 16, 17], [0, 21, 5, 11, 8, 27], [14, 20, 5, 7, 21, 30], [6, 26, 29, 24, 13, 27]], ![[28, 16, 14, 23, 9, 11], [3, 28, 20, 23, 4, 12], [24, 9, 21, 9, 6, 21], [16, 22, 16, 1, 14, 30]]]
 h' := ![![[2, 26, 11, 2], [8, 30, 26, 19], [11, 0, 15, 21], [0, 0, 0, 1], [0, 1]], ![[29, 23, 24, 3], [21, 10, 28, 10], [7, 4, 27, 21], [20, 7, 9, 21], [2, 26, 11, 2]], ![[27, 12, 27, 26], [22, 30, 3, 4], [19, 6, 22, 3], [26, 20, 20, 17], [29, 23, 24, 3]], ![[0, 1], [9, 23, 5, 29], [23, 21, 29, 17], [6, 4, 2, 23], [27, 12, 27, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [9, 11, 20], []]
 b := ![[], [], [5, 6, 23, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 4
  hpos := by decide
  P := [15, 19, 17, 4, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![40327088912060, -473995333710761, -310318605575311, 425926371534581, 711925370776958]
  a := ![-971, -183, 243, -1091, -2792]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-343179144282010, -153082179302339, -653039644752585, -491497799534145, 711925370776958]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 923521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, 3, 2, -3, -8]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-17, 3, 2, -3, -8]] 
 ![![31, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![-17, 3, 2, -3, -8], ![24, 2, -1, 0, 3], ![-18, 16, 6, -12, -27], ![24, 21, 4, -11, -19], ![-6, -6, -1, 3, 5]]]
  hmulB := by decide  
  f := ![![![-5, -2, 1, 3, 10]], ![![-6, -3, 1, 3, 9]], ![![0, -1, -1, 6, 18]], ![![-12, -7, 2, 4, 11]], ![![-1, 0, 0, 3, 10]]]
  g := ![![![5, 3, 2, -3, -8], ![-3, 2, -1, 0, 3], ![15, 16, 6, -12, -27], ![5, 21, 4, -11, -19], ![-1, -6, -1, 3, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-5, -2, 1, 3, 10]] ![![-17, 3, 2, -3, -8]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25220616817, 2474820498, 2463713451, -3141903501, -9276924706]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-25220616817, 2474820498, 2463713451, -3141903501, -9276924706]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![5, 19, 27, 1, 0], ![24, 14, 15, 0, 1]] where
  M :=![![![-25220616817, 2474820498, 2463713451, -3141903501, -9276924706], ![30526320228, -2995459651, -2982010657, 3802879461, 11228541831], ![-36948215298, 3625584853, 3609333915, -4602862854, -13590648876], ![12766365118, -1252780079, -1247116324, 1590445480, 4695962399], ![-1990159914, 195300256, 194414861, -247939710, -732064412]]]
  hmulB := by decide  
  f := ![![![46355873, 14178325, -17189692, 10803465, 18459722]], ![![-24330612, 18969864, 28220809, 1086408, 82342197]], ![![-485361918, -298491604, 70918436, -151500084, -716092389]], ![![-337215865, -195701692, 57763703, -102269474, -456815343]], ![![-190827456, -111225382, 32339391, -57996063, -260178680]]]
  g := ![![![5760407936, 5190484673, 6120242664, -3141903501, -9276924706], ![-6972245433, -6282425812, -7407780637, 3802879461, 11228541831], ![8438964108, 7604028739, 8966117949, -4602862854, -13590648876], ![-2915917834, -2627424805, -3098069737, 1590445480, 4695962399], ![454569852, 409596122, 482966303, -247939710, -732064412]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [36, 2, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 11, 18], [20, 25, 19], [0, 1]]
 g := ![![[26, 29, 12], [27, 25], [10, 18, 25], [9, 1], []], ![[4, 27, 9, 24], [5, 4], [33, 10, 9, 29], [18, 33], [19, 28]], ![[13, 26, 33, 15], [5, 9], [10, 20, 36, 22], [10, 10], [18, 28]]]
 h' := ![![[26, 11, 18], [16, 34, 7], [10, 5, 32], [9, 20, 5], [0, 0, 1], [0, 1]], ![[20, 25, 19], [30, 16, 10], [32, 20, 2], [8, 33, 4], [29, 7, 25], [26, 11, 18]], ![[0, 1], [33, 24, 20], [18, 12, 3], [20, 21, 28], [11, 30, 11], [20, 25, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 6], []]
 b := ![[], [4, 5, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [36, 2, 28, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21968251, 31812453, 5709252, -24822996, -55660567]
  a := ![-65, -11, 17, -75, -187]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![40052347, 34667495, 40833477, -24822996, -55660567]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0, 0, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![1, 1, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![25, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, -1, 0, 3, 0], ![8, 1, -2, 11, 23], ![-6, -3, 1, -3, -8]]]
  hmulB := by decide  
  f := ![![![-185, 21, 19, -24, -69]], ![![1, 0, 0, 0, 0]], ![![-186, 22, 19, -24, -69]], ![![-123, 14, 13, -16, -46]], ![![-70, 8, 7, -9, -26]]]
  g := ![![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-2, -1, 0, 3, 0], ![-14, 1, -2, 11, 23], ![4, -3, 1, -3, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21964333, 9729147, -5956000, 5889234, 19239013]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![21964333, 9729147, -5956000, 5889234, 19239013]] 
 ![![37, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![21964333, 9729147, -5956000, 5889234, 19239013], ![-68320206, -23907472, 23145692, -16692699, -37698735], ![92650818, 4937608, -51366501, 15606291, -44643462], ![139013904, 91528044, -15924248, 44935795, 226131218], ![-100414470, -62515245, 14118422, -31538043, -150803050]]]
  hmulB := by decide  
  f := ![![![-5305703411, 520639153, 518297206, -660975960, -1951617125]], ![![-3841562174, 376966786, 375270230, -478576851, -1413058715]], ![![-4511996688, 442758248, 440763635, -562100967, -1659671868]], ![![-3225549541, 316525429, 315095794, -401840843, -1186479479]], ![![-1732085130, 169964617, 169201384, -215778717, -637116418]]]
  g := ![![![-11840333, 9729147, -5956000, 5889234, 19239013], ![20082031, -23907472, 23145692, -16692699, -37698735], ![45193775, 4937608, -51366501, 15606291, -44643462], ![-153868697, 91528044, -15924248, 44935795, 226131218], ![101661387, -62515245, 14118422, -31538043, -150803050]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-25220616817, 2474820498, 2463713451, -3141903501, -9276924706]] ![![1, 1, 0, 0, 0]]
  ![![5305703411, -520639153, -518297206, 660975960, 1951617125]] where
 M := ![![![5305703411, -520639153, -518297206, 660975960, 1951617125]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![5305703411, -520639153, -518297206, 660975960, 1951617125]] ![![21964333, 9729147, -5956000, 5889234, 19239013]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 67, 10, -42, -66]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![131, 67, 10, -42, -66]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![21, 17, 16, 23, 1]] where
  M :=![![![131, 67, 10, -42, -66], ![60, 277, 75, -192, -372], ![696, 909, 214, -579, -1068], ![844, 1431, 358, -905, -1715], ![-222, -373, -93, 243, 458]]]
  hmulB := by decide  
  f := ![![![1, -1, -1, 0, -3]], ![![18, 11, -3, 6, 27]], ![![-114, -54, 29, -30, -105]], ![![98, 33, -34, 26, 59]], ![![17, 1, -9, 5, 1]]]
  g := ![![![37, 29, 26, 36, -66], ![192, 161, 147, 204, -372], ![564, 465, 422, 585, -1068], ![899, 746, 678, 940, -1715], ![-240, -199, -181, -251, 458]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 4 2 5 [8, 0, 34, 19, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 15, 22, 14], [2, 26, 24, 5], [24, 40, 36, 22], [0, 1]]
 g := ![![[21, 14, 1, 25], [15, 32, 33], [22, 1, 1], [22, 1], []], ![[31, 36, 34, 29, 30, 7], [29, 5, 36], [5, 32, 36], [24, 12, 5, 27, 34, 26], [33, 8, 32]], ![[39, 0, 9, 5], [11, 5, 16], [26, 6, 16], [25, 5, 13, 17, 14, 16], [23, 11, 25]], ![[34, 14, 9, 36, 37, 12], [39, 10, 2], [18, 35, 9], [17, 30, 37, 30, 20, 3], [28, 14, 33]]]
 h' := ![![[37, 15, 22, 14], [2, 22, 18, 36], [9, 20, 40, 19], [29, 33, 31, 40], [0, 0, 1], [0, 1]], ![[2, 26, 24, 5], [32, 4, 19, 12], [10, 35, 28, 35], [38, 13, 36, 35], [39, 21, 24, 18], [37, 15, 22, 14]], ![[24, 40, 36, 22], [2, 33, 40], [7, 14, 13, 4], [25, 16, 8, 4], [25, 16, 36, 6], [2, 26, 24, 5]], ![[0, 1], [36, 23, 5, 34], [15, 13, 1, 24], [35, 20, 7, 3], [24, 4, 21, 17], [24, 40, 36, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [21, 12, 10], []]
 b := ![[], [], [19, 22, 2, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 4
  hpos := by decide
  P := [8, 0, 34, 19, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1358675415516, -12384587122787, -8263140916643, 11399793333867, 19355135350047]
  a := ![391, 72, -97, 439, 1124]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9880467486231, -8327363123746, -7754763573595, -10579715115054, 19355135350047]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 2825761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, 1, 0, 3]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-1, 1, 1, 0, 3]] 
 ![![41, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] where
  M :=![![![-1, 1, 1, 0, 3], ![-18, -11, 3, -6, -27], ![114, 54, -29, 30, 105], ![-98, -33, 34, -26, -59], ![60, 20, -21, 15, 32]]]
  hmulB := by decide  
  f := ![![![-131, -67, -10, 42, 66]], ![![-43, -28, -5, 18, 30]], ![![-132, -81, -14, 51, 84]], ![![-142, -97, -18, 61, 103]], ![![-116, -53, -7, 33, 50]]]
  g := ![![![-4, 1, 1, 0, 3], ![31, -11, 3, -6, -27], ![-114, 54, -29, 30, 105], ![57, -33, 34, -26, -59], ![-30, 20, -21, 15, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![131, 67, 10, -42, -66]] ![![-1, 1, 1, 0, 3]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2815, -458, -328, 469, 1274]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![2815, -458, -328, 469, 1274]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![31, 34, 42, 11, 1]] where
  M :=![![![2815, -458, -328, 469, 1274], ![-3892, -210, 206, -116, -679], ![3146, -2177, -863, 1495, 3443], ![-3148, -2404, -506, 1137, 2054], ![692, 691, 158, -362, -674]]]
  hmulB := by decide  
  f := ![![![61, 14, -26, 13, 8]], ![![56, 76, 22, 28, 227]], ![![-1138, -619, 225, -335, -1399]], ![![1544, 652, -442, 405, 1238]], ![![-651, -377, 112, -198, -882]]]
  g := ![![![-853, -1018, -1252, -315, 1274], ![399, 532, 668, 171, -679], ![-2409, -2773, -3383, -846, 3443], ![-1554, -1680, -2018, -499, 2054], ![502, 549, 662, 164, -674]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [32, 7, 24, 19, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 23, 12, 17], [26, 31, 37, 8], [3, 31, 37, 18], [0, 1]]
 g := ![![[23, 31, 0, 1], [5, 10, 42, 16], [3, 7, 6], [24, 1], []], ![[36, 35, 17, 39, 14, 10], [33, 11, 13, 30, 42, 36], [40, 11, 21], [3, 40, 37, 28, 41, 38], [9, 34, 31]], ![[26, 12, 31, 33, 21, 42], [33, 22, 35, 31, 13, 12], [41, 29, 15], [23, 24, 41, 14, 41, 39], [16, 21, 21]], ![[31, 5, 41, 7, 25, 18], [8, 37, 1, 26, 19, 37], [30, 16, 9], [17, 17, 5, 9, 17, 32], [21, 35, 23]]]
 h' := ![![[38, 23, 12, 17], [12, 20, 31, 1], [26, 21, 11, 4], [6, 15, 19, 36], [0, 0, 1], [0, 1]], ![[26, 31, 37, 8], [17, 1, 34, 37], [3, 29, 36, 11], [37, 13, 12, 35], [38, 38, 38, 38], [38, 23, 12, 17]], ![[3, 31, 37, 18], [2, 0, 19, 4], [1, 24, 37, 18], [25, 5, 31, 12], [35, 11, 5, 35], [26, 31, 37, 8]], ![[0, 1], [1, 22, 2, 1], [33, 12, 2, 10], [41, 10, 24, 3], [25, 37, 42, 13], [3, 31, 37, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [11, 2, 41], []]
 b := ![[], [], [8, 30, 2, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [32, 7, 24, 19, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![122624792307, -18008160136, -78949188968, 80485337488, 151817487768]
  a := ![-119, -22, 28, -128, -342]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-106598077407, -120460528936, -150122876168, -36965279720, 151817487768]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-61, -14, 26, -13, -8]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-61, -14, 26, -13, -8]] 
 ![![43, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-61, -14, 26, -13, -8], ![-56, -76, -22, -28, -227], ![1138, 619, -225, 335, 1399], ![-1544, -652, 442, -405, -1238], ![976, 403, -286, 254, 752]]]
  hmulB := by decide  
  f := ![![![-2815, 458, 328, -469, -1274]], ![![-826, 154, 102, -150, -399]], ![![-1317, 253, 165, -242, -643]], ![![-2349, 450, 294, -430, -1144]], ![![-1129, 165, 126, -177, -488]]]
  g := ![![![6, -14, 26, -13, -8], ![147, -76, -22, -28, -227], ![-917, 619, -225, 335, 1399], ![819, -652, 442, -405, -1238], ![-498, 403, -286, 254, 752]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![2815, -458, -328, 469, 1274]] ![![-61, -14, 26, -13, -8]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![-43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
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


def P47P0 : CertificateIrreducibleZModOfList' 47 5 2 5 [38, 37, 46, 27, 24, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 37, 37, 44, 24], [19, 5, 4, 20, 2], [23, 33, 16, 35, 40], [31, 18, 37, 42, 28], [0, 1]]
 g := ![![[31, 44, 11, 20, 9], [15, 26, 27, 2, 24], [16, 42, 41, 21, 12], [1], []], ![[10, 19, 36, 15, 19, 40, 16, 25], [29, 21, 39, 41, 18, 44, 3, 18], [39, 34, 24, 24, 28, 5, 32, 18], [1, 9, 7, 23, 18, 15, 41, 25], [7, 32, 38, 12]], ![[41, 36, 35, 18, 16, 40, 9, 16], [25, 42, 25, 33, 12, 39, 19, 4], [46, 37, 26, 33, 26, 8, 20, 6], [22, 9, 6, 8, 43, 24, 45, 27], [35, 34, 31, 4]], ![[43, 9, 43, 3, 16, 41, 36, 5], [13, 40, 3, 15, 16, 13, 0, 35], [40, 26, 14, 25, 29, 25, 34, 5], [8, 44, 12, 11, 43, 15, 41, 29], [8, 41, 26, 2]], ![[2, 23, 44, 22, 21, 13, 27, 3], [27, 6, 28, 25, 40, 38, 41, 28], [43, 17, 34, 26, 22, 25, 21, 9], [0, 32, 28, 44, 11, 4, 34, 9], [5, 18, 33, 32]]]
 h' := ![![[44, 37, 37, 44, 24], [41, 17, 2, 8, 3], [3, 8, 45, 45, 20], [9, 10, 1, 20, 23], [0, 0, 1], [0, 1]], ![[19, 5, 4, 20, 2], [14, 19, 37, 9, 12], [45, 12, 12, 20, 6], [14, 43, 7, 17, 6], [25, 42, 30, 32, 35], [44, 37, 37, 44, 24]], ![[23, 33, 16, 35, 40], [3, 5, 33, 5, 14], [26, 39, 14, 46, 40], [9, 41, 38, 37, 35], [18, 0, 32, 0, 15], [19, 5, 4, 20, 2]], ![[31, 18, 37, 42, 28], [17, 26, 17, 7, 37], [24, 28, 38, 21, 29], [22, 40, 8, 9, 37], [37, 40, 33, 43, 4], [23, 33, 16, 35, 40]], ![[0, 1], [30, 27, 5, 18, 28], [34, 7, 32, 9, 46], [5, 7, 40, 11, 40], [19, 12, 45, 19, 40], [31, 18, 37, 42, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 4, 19, 14], [], [], []]
 b := ![[], [39, 21, 16, 15, 19], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 5
  hpos := by decide
  P := [38, 37, 46, 27, 24, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-54363922302522, -39037908282844, 3869273800842, -18402871464148, -99736817720312]
  a := ![64, 20, -6, 44, 184]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1156679197926, -830593793252, 82324974486, -391550456684, -2122059951496]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![202585, 82995, -59834, 52594, 153961]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![202585, 82995, -59834, 52594, 153961]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![35, 14, 39, 22, 1]] where
  M :=![![![202585, 82995, -59834, 52594, 153961], ![-503014, -146870, 191602, -115445, -175987], ![132362, -282100, -283569, -51683, -1071352], ![1881332, 1049778, -352828, 559797, 2402040], ![-1286962, -695271, 257968, -377099, -1563558]]]
  hmulB := by decide  
  f := ![![![-16686559, 1637389, 1630048, -2078752, -6137821]], ![![20196910, -1981896, -1972976, 2516087, 7429093]], ![![-24445862, 2398694, 2387999, -3045337, -8991836]], ![![8446456, -828964, -825148, 1052295, 3107010]], ![![-20191625, 1981192, 1972403, -2515336, -7426947]]]
  g := ![![![-97850, -39103, -114421, -62916, 153961], ![106727, 43716, 133115, 70873, -175987], ![709994, 277676, 783003, 443737, -1071352], ![-1550756, -614694, -1774196, -986511, 2402040], ![1008256, 399897, 1155410, 641909, -1563558]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [44, 24, 17, 30, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 25, 16, 36], [13, 32, 22, 41], [44, 48, 15, 29], [0, 1]]
 g := ![![[8, 15, 16, 11], [15, 48, 11], [41, 4, 39, 43], [35, 23, 1], []], ![[27, 23, 28, 45, 43, 1], [15, 44, 11], [8, 14, 46, 22, 11, 4], [12, 37, 7], [22, 24, 5, 6, 36, 16]], ![[24, 44, 48, 12, 32, 41], [25, 37, 9], [22, 19, 40, 43, 46, 21], [17, 29, 10], [36, 46, 52, 17, 23, 21]], ![[29, 0, 40, 39, 44, 10], [49, 12, 9], [28, 51, 46, 31, 52, 25], [48, 24, 47], [36, 45, 32, 30, 51, 9]]]
 h' := ![![[19, 25, 16, 36], [33, 12, 15, 8], [51, 15, 17, 8], [50, 3, 28, 19], [0, 0, 0, 1], [0, 1]], ![[13, 32, 22, 41], [38, 44, 18, 44], [50, 34, 23, 45], [13, 13, 14, 35], [8, 51, 2, 22], [19, 25, 16, 36]], ![[44, 48, 15, 29], [23, 35, 34, 52], [40, 21, 7, 3], [46, 31, 30, 12], [30, 33, 22, 40], [13, 32, 22, 41]], ![[0, 1], [33, 15, 39, 2], [4, 36, 6, 50], [51, 6, 34, 40], [19, 22, 29, 43], [44, 48, 15, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [35, 52, 32], []]
 b := ![[], [], [8, 42, 48, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [44, 24, 17, 30, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2636771972, 843149028, -785613606, 1906926042, 6335165382]
  a := ![-13, -6, -1, 4, -39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4133849366, -1657531440, -4676548368, -2593711554, 6335165382]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16686559, 1637389, 1630048, -2078752, -6137821]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-16686559, 1637389, 1630048, -2078752, -6137821]] 
 ![![53, 0, 0, 0, 0], ![33, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![20, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![-16686559, 1637389, 1630048, -2078752, -6137821], ![20196910, -1981896, -1972976, 2516087, 7429093], ![-24445862, 2398694, 2387999, -3045337, -8991836], ![8446456, -828964, -825148, 1052295, 3107010], ![-1316714, 129247, 128638, -164053, -484374]]]
  hmulB := by decide  
  f := ![![![202585, 82995, -59834, 52594, 153961]], ![![116647, 48905, -33640, 30569, 92542]], ![![94234, 32260, -32445, 22841, 49504]], ![![111944, 51126, -29236, 30409, 103420]], ![![21586, 5673, -8680, 4793, 5358]]]
  g := ![![![101648, 1637389, 1630048, -2078752, -6137821], ![-123018, -1981896, -1972976, 2516087, 7429093], ![148944, 2398694, 2387999, -3045337, -8991836], ![-51400, -828964, -825148, 1052295, 3107010], ![8007, 129247, 128638, -164053, -484374]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![202585, 82995, -59834, 52594, 153961]] ![![-16686559, 1637389, 1630048, -2078752, -6137821]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![42543, -4217, -4168, 5330, 15708]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![42543, -4217, -4168, 5330, 15708]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![11, 54, 1, 0, 0], ![22, 13, 0, 1, 0], ![24, 8, 0, 0, 1]] where
  M :=![![![42543, -4217, -4168, 5330, 15708], ![-51608, 4917, 4999, -6328, -18782], ![62068, -6589, -6208, 8063, 23494], ![-22000, 1395, 1926, -2247, -7095], ![3478, -139, -281, 299, 1010]]]
  hmulB := by decide  
  f := ![![![4119, 1863, -1089, 1114, 3741]], ![![-13534, -4901, 4465, -3350, -8047]], ![![-11255, -4091, 3702, -2790, -6746]], ![![-1062, -114, 547, -194, 310]], ![![-444, -94, 195, -93, -32]]]
  g := ![![![-6879, 439, -4168, 5330, 15708], ![8193, -551, 4999, -6328, -18782], ![-10354, 608, -6208, 8063, 23494], ![2992, -282, 1926, -2247, -7095], ![-411, 52, -281, 299, 1010]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [21, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 58], [0, 1]]
 g := ![![[33, 45], [25, 35], [3], [2, 21], [15, 1]], ![[0, 14], [19, 24], [3], [22, 38], [30, 58]]]
 h' := ![![[15, 58], [6, 35], [49, 25], [17, 48], [39, 27], [0, 1]], ![[0, 1], [0, 24], [11, 34], [29, 11], [31, 32], [15, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [34, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [21, 44, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10382, -12786, -1506, 6973, 9309]
  a := ![-23, -4, 7, -29, -66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6282, -1637, -1506, 6973, 9309]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12106722889, 1187995378, 1182663305, -1508217357, -4453229124]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-12106722889, 1187995378, 1182663305, -1508217357, -4453229124]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![49, 54, 1, 0, 0], ![39, 6, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![-12106722889, 1187995378, 1182663305, -1508217357, -4453229124], ![14653635888, -1437916179, -1431462337, 1825503717, 5390062905], ![-17736347694, 1740413227, 1732601629, -2209538556, -6523980654], ![6128287890, -601349623, -598650884, 763442150, 2254173783], ![-955344894, 93745018, 93324293, -119013738, -351405376]]]
  hmulB := by decide  
  f := ![![![-6046181, -2942855, 1447124, -1688859, -6218274]], ![![23798772, 9472658, -7230535, 6107604, 17120709]], ![![15847583, 5984719, -5049680, 3984387, 10274769]], ![![-1826229, -1272170, 158486, -608170, -3213783]], ![![-3768267, -1732585, 975727, -1026600, -3521701]]]
  g := ![![![2753206575, -908924050, 1182663305, -1508217357, -4453229124], ![-3332403523, 1100136063, -1431462337, 1825503717, 5390062905], ![4033447825, -1331573617, 1732601629, -2209538556, -6523980654], ![-1393641359, 460087207, -598650884, 763442150, 2254173783], ![217256105, -71723464, 93324293, -119013738, -351405376]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [26, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 58], [0, 1]]
 g := ![![[14, 25], [48, 57], [16], [4, 48], [49, 1]], ![[0, 34], [9, 2], [16], [55, 11], [39, 58]]]
 h' := ![![[49, 58], [50, 5], [16, 23], [14, 55], [24, 15], [0, 1]], ![[0, 1], [0, 54], [22, 36], [54, 4], [51, 44], [49, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [32, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [26, 10, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-45747, -89528, -25259, 61940, 76042]
  a := ![77, 14, -16, 85, 221]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-71006, 15302, -25259, 61940, 76042]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1899567075, -828606139, 524412034, -506048102, -1619229981]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-1899567075, -828606139, 524412034, -506048102, -1619229981]] 
 ![![59, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![-1899567075, -828606139, 524412034, -506048102, -1619229981], ![5666995070, 1927662732, -1960151950, 1370445025, 2933963483], ![-6640220698, 195701596, 4080888115, -977896049, 5114564228], ![-13161259796, -8306444406, 1768635324, -4162479951, -20158053156], ![9370007714, 5632122523, -1463821492, 2891400571, 13370216344]]]
  hmulB := by decide  
  f := ![![![485268380359083, -47617890815115, -47404166852796, 60453204629036, 178496799909663]], ![![72293705782460, -7093958576936, -7062118675232, 9006121903277, 26591872989449]], ![![160097440183088, -15709868468248, -15639357672081, 19944434264029, 58888816795166]], ![![226133512219612, -22189784729032, -22090190044460, 28170999887671, 83178937509786]], ![![255620550089657, -25083256887394, -24970675398986, 31844402081741, 94025186944771]]]
  g := ![![![1039195830, -828606139, 524412034, -506048102, -1619229981], ![-1824613997, 1927662732, -1960151950, 1370445025, 2933963483], ![-3613959736, 195701596, 4080888115, -977896049, 5114564228], ![13212149744, -8306444406, 1768635324, -4162479951, -20158053156], ![-8746412768, 5632122523, -1463821492, 2891400571, 13370216344]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![42543, -4217, -4168, 5330, 15708]] ![![-12106722889, 1187995378, 1182663305, -1508217357, -4453229124]]
  ![![-485268380359083, 47617890815115, 47404166852796, -60453204629036, -178496799909663]] where
 M := ![![![-485268380359083, 47617890815115, 47404166852796, -60453204629036, -178496799909663]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-485268380359083, 47617890815115, 47404166852796, -60453204629036, -178496799909663]] ![![-1899567075, -828606139, 524412034, -506048102, -1619229981]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34162521, 3352062, 3337154, -4255774, -12565841]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-34162521, 3352062, 3337154, -4255774, -12565841]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![48, 46, 48, 1, 0], ![37, 5, 2, 0, 1]] where
  M :=![![![-34162521, 3352062, 3337154, -4255774, -12565841], ![41348854, -4057926, -4039385, 5151245, 15209767], ![-50048642, 4910183, 4888736, -6235006, -18409268], ![17291924, -1697441, -1689486, 2153397, 6359591], ![-2695460, 264880, 263449, -335752, -991551]]]
  hmulB := by decide  
  f := ![![![-147417, -58249, 45099, -37723, -104561]], ![![325582, 83444, -132463, 71750, 73420]], ![![133480, 309535, 145827, 99851, 989470]], ![![208986, 247063, 55630, 95558, 721383]], ![![-41119, -9430, 17535, -8778, -5410]]]
  g := ![![![10410668, 4294211, 3815508, -4255774, -12565841], ![-12601185, -5197771, -4618339, 5151245, 15209767], ![15252042, 6291259, 5589960, -6235006, -18409268], ![-5268459, -2172978, -1930684, 2153397, 6359591], ![821443, 338807, 301027, -335752, -991551]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [36, 44, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 22, 56], [31, 38, 5], [0, 1]]
 g := ![![[11, 50, 52], [33, 22], [20, 19, 46], [25, 35, 1], [1]], ![[3, 36, 3, 47], [39, 13], [8, 6, 29, 4], [55, 15, 33, 57], [11, 16, 0, 58]], ![[6, 16, 31, 15], [35, 5], [46, 51, 51, 20], [11, 17, 26, 27], [1, 49, 47, 3]]]
 h' := ![![[31, 22, 56], [54, 24, 33], [12, 3, 12], [15, 34, 31], [25, 17, 1], [0, 1]], ![[31, 38, 5], [41, 19, 36], [46, 14, 14], [27, 24, 32], [54, 24, 14], [31, 22, 56]], ![[0, 1], [26, 18, 53], [35, 44, 35], [24, 3, 59], [48, 20, 46], [31, 38, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 41], []]
 b := ![[], [57, 35, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [36, 44, 60, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-64130265, -65152103, -1314082, 39387993, 90485787]
  a := ![87, 16, -21, 95, 250]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-86929968, -38187356, -33982120, 39387993, 90485787]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73962689, -26073850, 24917783, -18120419, -41480864]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-73962689, -26073850, 24917783, -18120419, -41480864]] 
 ![![61, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![-73962689, -26073850, 24917783, -18120419, -41480864], ![103921832, 7441701, -56231659, 17991751, -43441861], ![404585174, 308470825, -15752003, 141548116, 804787022], ![-1062610066, -512187749, 257976652, -295532016, -1075377123], ![696132926, 328260038, -174298201, 191744746, 679121382]]]
  hmulB := by decide  
  f := ![![![-8257848897935, 810317262153, 806680307926, -1028736773399, -3037493600258]], ![![-648393868414, 63624891712, 63339323743, -80774863112, -238499426023]], ![![-3582688036209, 351558134681, 349980233638, -446319976549, -1317824061489]], ![![-66849477867, 6559731990, 6530290770, -8327896256, -24589314893]], ![![-5967163617590, 585539375664, 582911293815, -743370425403, -2194908326347]]]
  g := ![![![21357611, -26073850, 24917783, -18120419, -41480864], ![55057594, 7441701, -56231659, 17991751, -43441861], ![-600075685, 308470825, -15752003, 141548116, 804787022], ![707757796, -512187749, 257976652, -295532016, -1075377123], ![-442443571, 328260038, -174298201, 191744746, 679121382]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-256711, 25186, 25076, -31977, -94420]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-256711, 25186, 25076, -31977, -94420]] 
 ![![61, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![-256711, 25186, 25076, -31977, -94420], ![310704, -30504, -30356, 38718, 114309], ![-376110, 36851, 36725, -46815, -138267], ![129892, -12834, -12714, 16243, 47900], ![-20244, 2009, 1984, -2538, -7478]]]
  hmulB := by decide  
  f := ![![![8333, 3870, -2130, 2277, 7910]], ![![3892, 1850, -964, 1074, 3841]], ![![2663, 997, -855, 666, 1691]], ![![5935, 2956, -1372, 1672, 6326]], ![![3219, 1375, -910, 849, 2638]]]
  g := ![![![39472, 25186, 25076, -31977, -94420], ![-47785, -30504, -30356, 38718, 114309], ![57807, 36851, 36725, -46815, -138267], ![-20015, -12834, -12714, 16243, 47900], ![3124, 2009, 1984, -2538, -7478]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-34162521, 3352062, 3337154, -4255774, -12565841]] ![![-73962689, -26073850, 24917783, -18120419, -41480864]]
  ![![-8333, -3870, 2130, -2277, -7910]] where
 M := ![![![-8333, -3870, 2130, -2277, -7910]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![-8333, -3870, 2130, -2277, -7910]] ![![-256711, 25186, 25076, -31977, -94420]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![-61, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)


lemma PB540I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB540I1 : PrimesBelowBoundCertificateInterval O 23 61 540 where
  m := 9
  g := ![2, 2, 3, 2, 2, 1, 2, 3, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB540I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1, I61N2]
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
    · exact ![707281, 29]
    · exact ![923521, 31]
    · exact ![50653, 37, 37]
    · exact ![2825761, 41]
    · exact ![3418801, 43]
    · exact ![229345007]
    · exact ![7890481, 53]
    · exact ![3481, 3481, 59]
    · exact ![226981, 61, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
  β := ![I29N1, I31N1, I37N1, I37N2, I41N1, I43N1, I53N1, I59N2, I61N1, I61N2]
  Il := ![[I29N1], [I31N1], [I37N1, I37N2], [I41N1], [I43N1], [], [I53N1], [I59N2], [I61N1, I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
