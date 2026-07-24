
import IdealArithmetic.Examples.NF5_1_48600000_4.RI5_1_48600000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![91, -202, 53, 119, 60]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![91, -202, 53, 119, 60]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![2, 15, 12, 16, 1]] where
  M :=![![![91, -202, 53, 119, 60], ![360, -809, 217, 473, 238], ![1428, -3210, 854, 1883, 946], ![5676, -12762, 3403, 7476, 3766], ![10584, -23802, 6345, 13941, 7003]]]
  hmulB := by decide  
  f := ![![![23, 14, -1, -1, 0]], ![![0, 23, 13, -1, -2]], ![![-12, 30, 12, -1, -2]], ![![-12, 18, 19, -2, -2]], ![![-10, 35, 22, -2, -3]]]
  g := ![![![-1, -38, -23, -29, 60], ![-4, -151, -91, -115, 238], ![-16, -600, -362, -457, 946], ![-64, -2388, -1441, -1820, 3766], ![-118, -4443, -2679, -3383, 7003]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 4 2 4 [10, 8, 9, 24, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 25, 5, 18], [24, 3, 28, 14], [19, 0, 25, 26], [0, 1]]
 g := ![![[27, 12, 12, 22], [12, 6, 1], [27, 16, 5, 1], []], ![[18, 17, 17, 8, 24, 10], [19, 23, 1], [25, 4, 4, 7, 1, 27], [15, 5, 22, 2, 3, 3]], ![[16, 15, 2, 5, 19, 15], [19, 1, 4], [20, 15, 1, 20, 15, 15], [26, 19, 18, 24, 24, 18]], ![[0, 26, 19, 26, 1, 18], [8, 6, 4], [17, 4, 25, 6, 28, 27], [9, 15, 27, 15, 18, 2]]]
 h' := ![![[20, 25, 5, 18], [19, 0, 18, 15], [20, 1, 14, 28], [0, 0, 0, 1], [0, 1]], ![[24, 3, 28, 14], [4, 8, 2, 6], [7, 3, 9, 1], [20, 18, 11, 4], [20, 25, 5, 18]], ![[19, 0, 25, 26], [17, 5, 17, 17], [2, 20, 17, 2], [21, 1, 7, 17], [24, 3, 28, 14]], ![[0, 1], [0, 16, 21, 20], [14, 5, 18, 27], [12, 10, 11, 7], [19, 0, 25, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10, 23, 12], []]
 b := ![[], [], [14, 27, 23, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 4
  hpos := by decide
  P := [10, 8, 9, 24, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1416745894, -3177781106, 833882186, 1877182050, 950377048]
  a := ![0, -1, -3, -1, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16689938, -601152994, -364504910, -459615542, 950377048]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 707281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 14, -1, -1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![23, 14, -1, -1, 0]] 
 ![![29, 0, 0, 0, 0], ![26, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![23, 14, -1, -1, 0], ![0, 23, 13, -1, -2], ![-12, 30, 12, -1, -2], ![-12, 18, 19, -2, -2], ![0, -6, -3, 3, -1]]]
  hmulB := by decide  
  f := ![![![91, -202, 53, 119, 60]], ![![94, -209, 55, 123, 62]], ![![112, -250, 66, 147, 74]], ![![202, -454, 121, 266, 134]], ![![434, -974, 259, 571, 287]]]
  g := ![![![-11, 14, -1, -1, 0], ![-28, 23, 13, -1, -2], ![-34, 30, 12, -1, -2], ![-28, 18, 19, -2, -2], ![8, -6, -3, 3, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![91, -202, 53, 119, 60]] ![![23, 14, -1, -1, 0]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5501, 15262, -7173, -4735, 3040]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-5501, 15262, -7173, -4735, 3040]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![24, 5, 25, 4, 1]] where
  M :=![![![-5501, 15262, -7173, -4735, 3040], ![18240, -51101, 25727, 14107, -9470], ![-56820, 160290, -84344, -40563, 28214], ![169284, -480030, 260797, 113154, -81126], ![-214968, 612942, -344081, -133261, 99047]]]
  hmulB := by decide  
  f := ![![![277, -790, 383, 563, 268]], ![![1608, -3743, 1113, 2259, 1126]], ![![6756, -15282, 4146, 8995, 4518]], ![![27108, -61014, 16303, 35772, 17990]], ![![11052, -25081, 6900, 14819, 7435]]]
  g := ![![![-2531, 2, -2683, -545, 3040], ![7920, -121, 8467, 1677, -9470], ![-23676, 620, -25474, -4949, 28214], ![68268, -2400, 73837, 14118, -81126], ![-83616, 3797, -90976, -17079, 99047]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 4 2 4 [29, 24, 30, 10, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 14, 18, 18], [30, 3, 11, 19], [0, 13, 2, 25], [0, 1]]
 g := ![![[11, 13, 13, 9], [30, 11, 3, 25], [10, 8, 21, 1], []], ![[0, 12, 1, 29, 27, 2], [30, 1, 18, 18], [1, 10, 29, 23, 28, 5], [7, 11, 22, 16, 3, 4]], ![[25, 9, 4, 18, 17, 20], [8, 18, 15, 9, 15, 5], [19, 17, 1, 21, 4, 25], [20, 19, 11, 14, 22, 8]], ![[0, 21, 12, 3, 19, 7], [1, 14, 7, 12, 20, 14], [19, 3, 19, 13, 26, 18], [4, 16, 14, 17, 20, 1]]]
 h' := ![![[22, 14, 18, 18], [29, 12, 19, 28], [20, 24, 15, 26], [0, 0, 0, 1], [0, 1]], ![[30, 3, 11, 19], [10, 6, 4, 10], [28, 26, 30], [29, 1, 16, 23], [22, 14, 18, 18]], ![[0, 13, 2, 25], [22, 23, 23, 22], [5, 2, 10, 20], [8, 1, 26, 27], [30, 3, 11, 19]], ![[0, 1], [2, 21, 16, 2], [7, 10, 7, 16], [8, 29, 20, 11], [0, 13, 2, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [5, 24, 3], []]
 b := ![[], [], [20, 19, 17, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 4
  hpos := by decide
  P := [29, 24, 30, 10, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-521195092, 1458163140, -740165076, -388439439, 263691615]
  a := ![3, -64, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-220961092, 4506615, -236530821, -46555029, 263691615]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 923521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-277, 790, -383, -563, -268]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-277, 790, -383, -563, -268]] 
 ![![31, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![-277, 790, -383, -563, -268], ![-1608, 3743, -1113, -2259, -1126], ![-6756, 15282, -4146, -8995, -4518], ![-27108, 61014, -16303, -35772, -17990], ![-50592, 113730, -30281, -66619, -33513]]]
  hmulB := by decide  
  f := ![![![5501, -15262, 7173, 4735, -3040]], ![![3493, -9675, 4492, 3058, -1950]], ![![6979, -19448, 9431, 5738, -3754]], ![![-2799, 8100, -4942, -1359, 1146]], ![![12258, -34542, 18041, 8881, -6137]]]
  g := ![![![295, 790, -383, -563, -268], ![395, 3743, -1113, -2259, -1126], ![1047, 15282, -4146, -8995, -4518], ![3827, 61014, -16303, -35772, -17990], ![6982, 113730, -30281, -66619, -33513]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-5501, 15262, -7173, -4735, 3040]] ![![-277, 790, -383, -563, -268]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![58633, -16820, -23204, 100, 3284]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![58633, -16820, -23204, 100, 3284]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![26, 23, 17, 30, 1]] where
  M :=![![![58633, -16820, -23204, 100, 3284], ![19704, 9373, -300, -216, 200], ![1200, 16704, 10157, 1100, -432], ![-2592, 7680, 15644, 7133, 2200], ![6000, -26148, 7828, 14972, 7349]]]
  hmulB := by decide  
  f := ![![![16861, -47836, 26068, 11196, -8052]], ![![-48312, 137641, -76900, -30296, 22392]], ![![134352, -384192, 219305, 79844, -60592]], ![![-363552, 1043232, -607308, -204839, 159688]], ![![-240094, 689199, -401979, -134546, 105181]]]
  g := ![![![-723, -2496, -2136, -2660, 3284], ![392, 129, -100, -168, 200], ![336, 720, 473, 380, -432], ![-1616, -1160, -588, -1591, 2200], ![-5002, -5275, -3165, -5554, 7349]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 4 2 5 [12, 17, 32, 24, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 32, 32, 29], [13, 31, 14, 16], [5, 10, 28, 29], [0, 1]]
 g := ![![[22, 22, 15, 9], [1], [33, 6, 33, 21], [1], []], ![[16, 27, 24, 17, 22, 29], [33, 7, 1], [20, 9, 30, 15, 34, 32], [16, 35, 10], [34, 24, 27]], ![[35, 5, 29, 19, 26, 28], [14, 1, 36], [23, 31, 21, 3, 10, 33], [26, 33, 11], [15, 2, 34]], ![[18, 7, 28, 13, 21, 14], [9, 21, 12], [35, 30, 32, 14, 20, 5], [13, 23, 9], [16, 14, 27]]]
 h' := ![![[32, 32, 32, 29], [35, 29, 17, 34], [11, 29, 1], [25, 20, 5, 13], [0, 0, 1], [0, 1]], ![[13, 31, 14, 16], [12, 23, 29, 36], [1, 1, 34, 1], [14, 26, 6, 25], [24, 35, 31, 11], [32, 32, 32, 29]], ![[5, 10, 28, 29], [29, 30, 25, 14], [7, 20, 32, 6], [31, 0, 13, 34], [26, 9, 33, 23], [13, 31, 14, 16]], ![[0, 1], [13, 29, 3, 27], [26, 24, 7, 30], [20, 28, 13, 2], [18, 30, 9, 3], [5, 10, 28, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [6, 15, 7], []]
 b := ![[], [], [23, 22, 6, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 4
  hpos := by decide
  P := [12, 17, 32, 24, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![62840774, -141323151, 37694362, 82753171, 41592328]
  a := ![1, -3, -1, -1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-27528642, -29674235, -18091222, -31486937, 41592328]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1874161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16861, -47836, 26068, 11196, -8052]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![16861, -47836, 26068, 11196, -8052]] 
 ![![37, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![16861, -47836, 26068, 11196, -8052], ![-48312, 137641, -76900, -30296, 22392], ![134352, -384192, 219305, 79844, -60592], ![-363552, 1043232, -607308, -204839, 159688], ![411888, -1187340, 708764, 215332, -174543]]]
  hmulB := by decide  
  f := ![![![58633, -16820, -23204, 100, 3284]], ![![22718, -6111, -8788, 32, 1248]], ![![41234, -11368, -16031, 100, 2296]], ![![9438, -2520, -3340, 209, 592]], ![![30271, -9344, -11704, 456, 1885]]]
  g := ![![![2557, -47836, 26068, 11196, -8052], ![-5934, 137641, -76900, -30296, 22392], ![13062, -384192, 219305, 79844, -60592], ![-26590, 1043232, -607308, -204839, 159688], ![17057, -1187340, 708764, 215332, -174543]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![58633, -16820, -23204, 100, 3284]] ![![16861, -47836, 26068, 11196, -8052]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -19, 11, 2, -2]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![11, -19, 11, 2, -2]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![10, 3, 36, 1, 0], ![25, 33, 10, 0, 1]] where
  M :=![![![11, -19, 11, 2, -2], ![-12, 41, -27, -3, 4], ![24, -72, 58, 1, -6], ![-36, 114, -101, 16, 2], ![-6, 3, 41, -44, 19]]]
  hmulB := by decide  
  f := ![![![7, 5, 1, 0, 0]], ![![0, 7, 5, 1, 0]], ![![0, 0, 8, 5, 2]], ![![2, 1, 8, 5, 2]], ![![5, 7, 7, 3, 1]]]
  g := ![![![1, 1, -1, 2, -2], ![-2, -2, 1, -3, 4], ![4, 3, 2, 1, -6], ![-6, 0, -17, 16, 2], ![-1, -12, 35, -44, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [22, 23, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 3, 26], [3, 37, 15], [0, 1]]
 g := ![![[40, 30, 31], [0, 21], [32, 31], [28, 25, 1], []], ![[40, 39, 31, 27], [30, 21], [24, 40], [4, 37, 15, 6], [0, 20]], ![[2, 38, 36, 15], [], [39, 21], [30, 38, 22, 12], [11, 20]]]
 h' := ![![[22, 3, 26], [36, 34, 21], [35, 27, 29], [40, 36, 21], [0, 0, 1], [0, 1]], ![[3, 37, 15], [1, 30, 21], [28, 5, 12], [8, 36, 32], [33, 20, 37], [22, 3, 26]], ![[0, 1], [1, 18, 40], [1, 9], [11, 10, 29], [13, 21, 3], [3, 37, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 17], []]
 b := ![[], [5, 20, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [22, 23, 16, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3948896, -8517113, 1736437, 5662894, 3240894]
  a := ![1, 19, 4, -1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3261034, -3230617, -5720407, 5662894, 3240894]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 5, 1, 0, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![7, 5, 1, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![7, 5, 1, 0, 0], ![6, 23, 0, 1, 0], ![39, 25, 0, 0, 1]] where
  M :=![![![7, 5, 1, 0, 0], ![0, 7, 5, 1, 0], ![0, 0, 8, 5, 2], ![12, -30, 15, 22, 10], ![30, -69, 17, 40, 21]]]
  hmulB := by decide  
  f := ![![![11, -19, 11, 2, -2]], ![![-12, 41, -27, -3, 4]], ![![1, 0, 0, 0, 0]], ![![-6, 23, -16, -1, 2]], ![![3, 7, -5, -1, 1]]]
  g := ![![![0, 0, 1, 0, 0], ![-1, -1, 5, 1, 0], ![-4, -5, 8, 5, 2], ![-15, -21, 15, 22, 10], ![-28, -39, 17, 40, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [7, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 40], [0, 1]]
 g := ![![[20, 9], [2], [39], [40, 2], [1]], ![[31, 32], [2], [39], [6, 39], [1]]]
 h' := ![![[24, 40], [19, 38], [22, 24], [7, 11], [34, 24], [0, 1]], ![[0, 1], [29, 3], [24, 17], [25, 30], [36, 17], [24, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [18, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [7, 17, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-795, 5604, -6267, 2863, 7388]
  a := ![-1, 0, -4, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6396, -5210, -6267, 2863, 7388]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![11, -19, 11, 2, -2]] ![![7, 5, 1, 0, 0]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-75265, 97355, 55411, -9306, -11788]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-75265, 97355, 55411, -9306, -11788]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![20, 2, 38, 1, 0], ![7, 15, 32, 0, 1]] where
  M :=![![![-75265, 97355, 55411, -9306, -11788], ![-70728, 101555, 29109, -27105, -18612], ![-111672, 208452, -18610, -101175, -54210], ![-325260, 701478, -163773, -398080, -202350], ![-551214, 1250769, -344871, -739524, -370975]]]
  hmulB := by decide  
  f := ![![![-309967, 910993, -600277, -107976, 110758]], ![![664548, -1971337, 1356807, 175029, -215952]], ![![-1295712, 3903828, -2876068, -154857, 350058]], ![![-1209464, 3629676, -2629843, -188830, 343622]], ![![-789433, 2398849, -1830381, -31227, 189237]]]
  g := ![![![4497, 6809, 18285, -9306, -11788], ![13992, 10115, 38481, -27105, -18612], ![53286, 28464, 129320, -101175, -54210], ![210530, 105416, 498569, -398080, -202350], ![391537, 192894, 921587, -739524, -370975]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [38, 26, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 33, 25], [34, 9, 18], [0, 1]]
 g := ![![[16, 14, 23], [15, 21, 15], [22, 14], [27, 28, 1], []], ![[36, 7, 41, 13], [26, 9, 18, 31], [14, 6], [34, 28, 29, 4], [15, 23]], ![[39, 19, 11, 26], [2, 8], [35, 9], [25, 23, 15, 37], [22, 23]]]
 h' := ![![[37, 33, 25], [32, 4, 18], [17, 21, 12], [6, 40, 33], [0, 0, 1], [0, 1]], ![[34, 9, 18], [28, 8, 4], [19, 37, 31], [32, 32, 7], [25, 17, 9], [37, 33, 25]], ![[0, 1], [37, 31, 21], [13, 28], [15, 14, 3], [19, 26, 33], [34, 9, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 21], []]
 b := ![[], [28, 4, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [38, 26, 15, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5641954, 16054992, -8884888, -3617192, 2669616]
  a := ![0, 0, 4, -10, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1116618, -389648, 1003272, -3617192, 2669616]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -2, 0, 0, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![1, -2, 0, 0, 0]] 
 ![![43, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![1, -2, 0, 0, 0], ![0, 1, -2, 0, 0], ![0, 0, 1, -2, 0], ![0, 0, -2, 1, -4], ![-12, 30, -10, -14, 1]]]
  hmulB := by decide  
  f := ![![![-341, 278, 220, -8, -32]], ![![-171, 139, 110, -4, -16]], ![![-256, 208, 165, -6, -24]], ![![-128, 104, 82, -3, -12]], ![![-245, 200, 158, -6, -23]]]
  g := ![![![1, -2, 0, 0, 0], ![1, 1, -2, 0, 0], ![0, 0, 1, -2, 0], ![4, 0, -2, 1, -4], ![-3, 30, -10, -14, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![56167, -164159, 105263, 22402, -21150]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![56167, -164159, 105263, 22402, -21150]] 
 ![![43, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![56167, -164159, 105263, 22402, -21150], ![-126900, 373417, -247507, -42787, 44804], ![268824, -798960, 554650, 66121, -85574], ![-513444, 1552434, -1160709, -44368, 132242], ![262314, -849057, 807313, -150568, -1581]]]
  hmulB := by decide  
  f := ![![![-66191, 105755, 2807, -44904, -25436]], ![![-45111, 73738, 220, -32271, -18060]], ![![-15610, 32698, -7054, -18251, -9334]], ![![-98164, 188434, -27049, -97658, -51254]], ![![-152282, 302471, -51863, -161396, -83827]]]
  g := ![![![102490, -164159, 105263, 22402, -21150], ![-235747, 373417, -247507, -42787, 44804], ![512524, -798960, 554650, 66121, -85574], ![-1022736, 1552434, -1160709, -44368, 132242], ![615201, -849057, 807313, -150568, -1581]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-75265, 97355, 55411, -9306, -11788]] ![![1, -2, 0, 0, 0]]
  ![![66191, -105755, -2807, 44904, 25436]] where
 M := ![![![66191, -105755, -2807, 44904, 25436]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![66191, -105755, -2807, 44904, 25436]] ![![56167, -164159, 105263, 22402, -21150]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![-43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13189, 29640, -8003, -17435, -8762]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-13189, 29640, -8003, -17435, -8762]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![23, 45, 15, 1, 0], ![39, 3, 28, 0, 1]] where
  M :=![![![-13189, 29640, -8003, -17435, -8762], ![-52572, 118241, -31605, -69337, -34870], ![-209220, 470478, -125446, -275695, -138674], ![-832044, 1870890, -498587, -1096164, -551390], ![-1549560, 3484164, -928389, -2041311, -1026827]]]
  hmulB := by decide  
  f := ![![![1813, -5148, 2809, 1203, -866]], ![![-5196, 14803, -8275, -3253, 2406]], ![![14436, -41286, 23580, 8567, -6506]], ![![-311, 861, -411, -259, 168]], ![![10713, -30633, 17469, 6385, -4839]]]
  g := ![![![15522, 17883, 10614, -17435, -8762], ![61747, 71128, 42230, -69337, -34870], ![245533, 282825, 167933, -275695, -138674], ![976254, 1124520, 667719, -1096164, -551390], ![1818018, 2094120, 1243456, -2041311, -1026827]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [17, 36, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 27, 13], [38, 19, 34], [0, 1]]
 g := ![![[27, 18, 4], [28, 16, 1], [24, 11, 3], [15, 2, 1], []], ![[18, 22], [19, 41, 6, 38], [40, 3, 38, 29], [39, 35, 2, 40], [6, 28]], ![[29, 31, 38, 42], [44, 1, 16, 3], [12, 25, 32, 2], [44, 4, 32, 17], [32, 28]]]
 h' := ![![[11, 27, 13], [41, 26, 2], [15, 7, 1], [27, 37, 35], [0, 0, 1], [0, 1]], ![[38, 19, 34], [36, 36], [17, 44, 16], [18, 13, 18], [19, 43, 19], [11, 27, 13]], ![[0, 1], [9, 32, 45], [6, 43, 30], [33, 44, 41], [7, 4, 27], [38, 19, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 13], []]
 b := ![[], [41, 39, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [17, 36, 45, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2252673, 4667436, -612909, -3510363, -2219622]
  a := ![13, -1, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3511722, 3601971, 2429616, -3510363, -2219622]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1813, -5148, 2809, 1203, -866]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![1813, -5148, 2809, 1203, -866]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![24, 32, 1, 0, 0], ![31, 34, 0, 1, 0], ![3, 43, 0, 0, 1]] where
  M :=![![![1813, -5148, 2809, 1203, -866], ![-5196, 14803, -8275, -3253, 2406], ![14436, -41286, 23580, 8567, -6506], ![-39036, 112026, -65249, -21962, 17134], ![44184, -127380, 76077, 23061, -18709]]]
  hmulB := by decide  
  f := ![![![-13189, 29640, -8003, -17435, -8762]], ![![-52572, 118241, -31605, -69337, -34870]], ![![-46980, 105650, -28274, -61977, -31166]], ![![-64433, 144892, -38750, -84981, -42736]], ![![-81909, 184201, -49179, -107981, -54309]]]
  g := ![![![-2134, -2100, 2809, 1203, -866], ![6107, 6101, -8275, -3253, 2406], ![-16969, -17178, 23580, 8567, -6506], ![45880, 47020, -65249, -21962, 17134], ![-51924, -54073, 76077, 23061, -18709]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [31, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 46], [0, 1]]
 g := ![![[21, 17], [11, 3], [34, 24], [3, 2], [1]], ![[46, 30], [32, 44], [14, 23], [17, 45], [1]]]
 h' := ![![[7, 46], [35, 8], [27, 12], [1, 27], [16, 7], [0, 1]], ![[0, 1], [44, 39], [17, 35], [2, 20], [18, 40], [7, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [35, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [31, 40, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-398, 1296, -911, -49, 1019]
  a := ![-1, -3, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![424, -249, -911, -49, 1019]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-13189, 29640, -8003, -17435, -8762]] ![![1813, -5148, 2809, 1203, -866]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1915, 5415, -2891, -1328, 936]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-1915, 5415, -2891, -1328, 936]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![46, 52, 24, 1, 0], ![31, 35, 30, 0, 1]] where
  M :=![![![-1915, 5415, -2891, -1328, 936], ![5616, -15955, 8767, 3661, -2656], ![-15936, 45456, -25574, -9825, 7322], ![43932, -125766, 72241, 25680, -19650], ![-50982, 146613, -86381, -27742, 22019]]]
  hmulB := by decide  
  f := ![![![757, -141, -277, -10, 34]], ![![204, 247, 19, -39, -20]], ![![-120, 504, 108, -121, -78]], ![![794, 368, -173, -110, -30]], ![![497, 391, -95, -115, -45]]]
  g := ![![![569, 787, 17, -1328, 936], ![-1518, -2139, 11, 3661, -2656], ![3944, 5662, -178, -9825, 7322], ![-9966, -14592, 857, 25680, -19650], ![10237, 15444, -1531, -27742, 22019]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [29, 33, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 10, 13], [41, 42, 40], [0, 1]]
 g := ![![[45, 29, 11], [41, 43], [51, 27, 42], [37, 11], [1]], ![[3, 31, 19, 6], [25, 47], [23, 24, 36, 49], [6, 10], [29, 12, 15, 24]], ![[14, 47, 8, 36], [29, 28], [46, 49, 24, 38], [37, 17], [18, 17, 8, 29]]]
 h' := ![![[20, 10, 13], [2, 7, 45], [5, 1, 34], [33, 3, 28], [24, 20, 8], [0, 1]], ![[41, 42, 40], [32, 16, 20], [42, 1, 10], [1, 7, 49], [4, 42, 13], [20, 10, 13]], ![[0, 1], [44, 30, 41], [14, 51, 9], [33, 43, 29], [29, 44, 32], [41, 42, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 38], []]
 b := ![[], [24, 34, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [29, 33, 45, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1121290, 4429458, -3783216, 678495, 2889591]
  a := ![3, 0, 7, -4, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2300177, -2490339, -2014242, 678495, 2889591]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![833, -2219, 735, 1000, -568]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![833, -2219, 735, 1000, -568]] 
 ![![53, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![833, -2219, 735, 1000, -568], ![-3408, 9353, -4059, -3241, 2000], ![12000, -33408, 16112, 9941, -6482], ![-38892, 109230, -55877, -29262, 19882], ![53646, -151857, 81633, 36678, -26021]]]
  hmulB := by decide  
  f := ![![![-54095, 42193, 33669, -1218, -4894]], ![![-6678, 5141, 4123, -149, -600]], ![![-17627, 13669, 10923, -401, -1592]], ![![-4216, 3242, 2555, -124, -390]], ![![-6048, 4797, 3711, -198, -575]]]
  g := ![![![20, -2219, 735, 1000, -568], ![197, 9353, -4059, -3241, 2000], ![-1176, -33408, 16112, 9941, -6482], ![4781, 109230, -55877, -29262, 19882], ![-7803, -151857, 81633, 36678, -26021]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7793, 21129, -8292, -8211, 4878]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![-7793, 21129, -8292, -8211, 4878]] 
 ![![53, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![52, 0, 0, 0, 1]] where
  M :=![![![-7793, 21129, -8292, -8211, 4878], ![29268, -80963, 37308, 25854, -16422], ![-98532, 275598, -137219, -77646, 51708], ![310248, -874152, 456492, 224737, -155292], ![-416610, 1182015, -644328, -276453, 198883]]]
  hmulB := by decide  
  f := ![![![-8281, 9141, -7860, -9561, -4464]], ![![-4099, 5074, -3840, -4887, -2298]], ![![-2321, 5079, -1583, -3135, -1560]], ![![-13542, 25146, -9876, -17177, -8436]], ![![-24770, 46407, -17664, -31299, -15407]]]
  g := ![![![-9298, 21129, -8292, -8211, 4878], ![36461, -80963, 37308, 25854, -16422], ![-125651, 275598, -137219, -77646, 51708], ![401742, -874152, 456492, 224737, -155292], ![-547301, 1182015, -644328, -276453, 198883]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-1915, 5415, -2891, -1328, 936]] ![![833, -2219, 735, 1000, -568]]
  ![![47119717, -135717184, 80646342, 24986098, -20101770]] where
 M := ![![![47119717, -135717184, 80646342, 24986098, -20101770]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![47119717, -135717184, 80646342, 24986098, -20101770]] ![![-7793, 21129, -8292, -8211, 4878]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![3840865466167, -11392607774245, 7837823311842, 1014897385681, -1249382826216]]]
 hmul := by decide  
 g := ![![![![72469159739, -214954863665, 147883458714, 19149007277, -23573260872]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13883, -40717, 26557, 5102, -5062]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![13883, -40717, 26557, 5102, -5062]] 
 ![![59, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![37, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![13883, -40717, 26557, 5102, -5062], ![-30372, 89813, -60925, -8877, 10204], ![61224, -183432, 131956, 10503, -17754], ![-106524, 327534, -261699, 7678, 21006], ![32406, -119091, 154143, -62580, 16555]]]
  hmulB := by decide  
  f := ![![![-10998803, 24730169, -6589631, -14489036, -7288324]], ![![-2418969, 5438942, -1449274, -3186597, -1602932]], ![![-9844477, 22134871, -5898111, -12968497, -6523454]], ![![-15631689, 35147493, -9365544, -20592416, -10358454]], ![![-22751555, 51156572, -13631426, -29971916, -15076551]]]
  g := ![![![-11595, -40717, 26557, 5102, -5062], ![26287, 89813, -60925, -8877, 10204], ![-55967, -183432, 131956, 10503, -17754], ![107835, 327534, -261699, 7678, 21006], ![-57079, -119091, 154143, -62580, 16555]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7643, 17183, -4578, -10067, -5064]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-7643, 17183, -4578, -10067, -5064]] 
 ![![59, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![-7643, 17183, -4578, -10067, -5064], ![-30384, 68317, -18204, -40026, -20134], ![-120804, 271626, -72379, -159142, -80052], ![-480312, 1079976, -287776, -632743, -318284], ![-894450, 2011161, -535904, -1178311, -592717]]]
  hmulB := by decide  
  f := ![![![443, -1339, 538, 393, -242]], ![![73, -226, 82, 67, -40]], ![![140, -406, 189, 110, -72]], ![![-130, 350, -236, -65, 56]], ![![473, -1378, 690, 340, -233]]]
  g := ![![![1068, 17183, -4578, -10067, -5064], ![4247, 68317, -18204, -40026, -20134], ![16886, 271626, -72379, -159142, -80052], ![67138, 1079976, -287776, -632743, -318284], ![125026, 2011161, -535904, -1178311, -592717]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, -59, -54, 1, 8]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![89, -59, -54, 1, 8]] 
 ![![59, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![47, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![52, 0, 0, 0, 1]] where
  M :=![![![89, -59, -54, 1, 8], ![48, -31, -18, 2, 2], ![12, 18, -19, -4, 4], ![24, -48, 34, 9, -8], ![-30, 63, -30, -9, 7]]]
  hmulB := by decide  
  f := ![![![-377, 847, -222, -495, -250]], ![![-166, 373, -98, -218, -110]], ![![-401, 901, -237, -527, -266]], ![![-580, 1304, -346, -763, -384]], ![![-1078, 2423, -642, -1419, -715]]]
  g := ![![![59, -59, -54, 1, 8], ![24, -31, -18, 2, 2], ![7, 18, -19, -4, 4], ![-6, -48, 34, 9, -8], ![-2, 63, -30, -9, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2

def I59N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -8, 27, 5, -6]] i)))

def SI59N3: IdealEqSpanCertificate' Table ![![-7, -8, 27, 5, -6]] 
 ![![59, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![44, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![-7, -8, 27, 5, -6], ![-36, 83, -33, -15, 10], ![60, -186, 118, 37, -30], ![-180, 510, -299, -92, 74], ![192, -552, 335, 91, -77]]]
  hmulB := by decide  
  f := ![![![619, -1340, 311, 759, 386]], ![![354, -769, 181, 437, 222]], ![![616, -1346, 324, 769, 390]], ![![1001, -2218, 562, 1283, 648]], ![![1277, -2860, 752, 1670, 841]]]
  g := ![![![-18, -8, 27, 5, -6], ![-11, 83, -33, -15, 10], ![-9, -186, 118, 37, -30], ![2, 510, -299, -92, 74], ![-6, -552, 335, 91, -77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N3 : Nat.card (O ⧸ I59N3) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N3)

lemma isPrimeI59N3 : Ideal.IsPrime I59N3 := prime_ideal_of_norm_prime hp59.out _ NI59N3

def I59N4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-32735, 42262, 28301, -1289, -4072]] i)))

def SI59N4: IdealEqSpanCertificate' Table ![![-32735, 42262, 28301, -1289, -4072]] 
 ![![59, 0, 0, 0, 0], ![44, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![52, 0, 0, 0, 1]] where
  M :=![![![-32735, 42262, 28301, -1289, -4072], ![-24432, 28345, 20613, -203, -2578], ![-15468, 14238, 15252, 2567, -406], ![-2436, -9378, 14775, 12410, 5134], ![23136, -46842, 6725, 24073, 12613]]]
  hmulB := by decide  
  f := ![![![-2119717, 6057730, -3445499, -1271487, 960460]], ![![-1483132, 4237517, -2407007, -892673, 673174]], ![![-653809, 1873600, -1082445, -376248, 290178]], ![![-1021933, 2900404, -1584172, -675179, 486730]], ![![-2574068, 7388114, -4306407, -1445101, 1128653]]]
  g := ![![![-32733, 42262, 28301, -1289, -4072], ![-22962, 28345, 20613, -203, -2578], ![-15411, 14238, 15252, 2567, -406], ![-10213, -9378, 14775, 12410, 5134], ![3778, -46842, 6725, 24073, 12613]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N4 : Nat.card (O ⧸ I59N4) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N4)

lemma isPrimeI59N4 : Ideal.IsPrime I59N4 := prime_ideal_of_norm_prime hp59.out _ NI59N4
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![13883, -40717, 26557, 5102, -5062]] ![![-7643, 17183, -4578, -10067, -5064]]
  ![![-193, 552, -313, -117, 88]] where
 M := ![![![-193, 552, -313, -117, 88]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-193, 552, -313, -117, 88]] ![![89, -59, -54, 1, 8]]
  ![![115, -199, -185, 318, -140]] where
 M := ![![![115, -199, -185, 318, -140]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N2 : IdealMulLeCertificate' Table 
  ![![115, -199, -185, 318, -140]] ![![-7, -8, 27, 5, -6]]
  ![![-88861, 256433, -154140, -45281, 37182]] where
 M := ![![![-88861, 256433, -154140, -45281, 37182]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N3 : IdealMulLeCertificate' Table 
  ![![-88861, 256433, -154140, -45281, 37182]] ![![-32735, 42262, 28301, -1289, -4072]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-1521433, 1470457, 1077163, -46374, -157530]]]
 hmul := by decide  
 g := ![![![![-25787, 24923, 18257, -786, -2670]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2, I59N3, I59N4] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
    exact isPrimeI59N3
    exact isPrimeI59N4
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1 ⊙ MulI59N2 ⊙ MulI59N3)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26539, 37169, 24015, -1340, -3570]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-26539, 37169, 24015, -1340, -3570]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![29, 29, 28, 1, 0], ![21, 5, 50, 0, 1]] where
  M :=![![![-26539, 37169, 24015, -1340, -3570], ![-21420, 27011, 17979, -975, -2680], ![-16080, 18780, 12636, -781, -1950], ![-11700, 13170, 8249, -1014, -1562], ![3354, -3525, -4145, -952, -39]]]
  hmulB := by decide  
  f := ![![![5669, -16571, 10633, 2254, -2132]], ![![-12792, 37649, -24977, -4291, 4508]], ![![27048, -80412, 55898, 6579, -8582]], ![![8185, -24336, 16925, 1983, -2594]], ![![23499, -69911, 48755, 5561, -7397]]]
  g := ![![![1431, 1539, 3935, -1340, -3570], ![1035, 1126, 2939, -975, -2680], ![779, 839, 2164, -781, -1950], ![828, 826, 1881, -1014, -1562], ![521, 398, 401, -952, -39]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [32, 5, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 46, 24], [1, 14, 37], [0, 1]]
 g := ![![[35, 2, 48], [49, 20], [58, 38, 56], [13, 38, 14], [1]], ![[16, 49, 36, 40], [9, 1], [55, 21, 40, 32], [47, 28, 58, 30], [36, 15, 0, 38]], ![[6, 52, 19, 38], [19, 3], [29, 58, 20, 11], [22, 33, 22, 50], [52, 60, 41, 23]]]
 h' := ![![[39, 46, 24], [23, 9, 29], [35, 18, 52], [11, 48, 19], [29, 56, 40], [0, 1]], ![[1, 14, 37], [31, 4, 12], [21, 15, 1], [26, 0, 15], [34, 8, 13], [39, 46, 24]], ![[0, 1], [3, 48, 20], [1, 28, 8], [40, 13, 27], [45, 58, 8], [1, 14, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 5], []]
 b := ![[], [19, 44, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [32, 5, 21, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![688775, -1286425, -28352, 1215579, 937129]
  a := ![1, 1, 2, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-889225, -675801, -1326574, 1215579, 937129]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -3, 2, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![1, -3, 2, 1, 0]] 
 ![![61, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![20, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![1, -3, 2, 1, 0], ![0, 1, -2, 2, 2], ![12, -30, 13, 12, 4], ![24, -48, 2, 41, 24], ![66, -153, 50, 79, 39]]]
  hmulB := by decide  
  f := ![![![1513, -1311, -1002, 39, 146]], ![![312, -269, -206, 8, 30]], ![![975, -843, -645, 25, 94]], ![![500, -432, -330, 13, 48]], ![![319, -276, -212, 8, 31]]]
  g := ![![![-1, -3, 2, 1, 0], ![0, 1, -2, 2, 2], ![-7, -30, 13, 12, 4], ![-10, -48, 2, 41, 24], ![-35, -153, 50, 79, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-425, 1286, -965, -33, 108]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-425, 1286, -965, -33, 108]] 
 ![![61, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![47, 0, 1, 0, 0], ![50, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![-425, 1286, -965, -33, 108], ![648, -2045, 1793, -209, -66], ![-396, 1638, -2584, 1331, -418], ![-2508, 5874, 879, -5510, 2662], ![8184, -22038, 8129, 9091, -5301]]]
  hmulB := by decide  
  f := ![![![6139, -6866, -3599, 991, 992]], ![![2211, -2507, -1254, 396, 374]], ![![4925, -5680, -2699, 976, 874]], ![![5690, -7078, -2579, 1654, 1238]], ![![4297, -6152, -1108, 2070, 1291]]]
  g := ![![![266, 1286, -965, -33, 108], ![-462, -2045, 1793, -209, -66], ![542, 1638, -2584, 1331, -418], ![423, 5874, 879, -5510, 2662], ![-3300, -22038, 8129, 9091, -5301]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-26539, 37169, 24015, -1340, -3570]] ![![1, -3, 2, 1, 0]]
  ![![-6139, 6866, 3599, -991, -992]] where
 M := ![![![-6139, 6866, 3599, -991, -992]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![-6139, 6866, 3599, -991, -992]] ![![-425, 1286, -965, -33, 108]]
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


lemma PB434I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB434I1 : PrimesBelowBoundCertificateInterval O 23 61 434 where
  m := 9
  g := ![2, 2, 2, 2, 3, 2, 3, 5, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB434I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1, I59N2, I59N3, I59N4]
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
    · exact ![1874161, 37]
    · exact ![68921, 1681]
    · exact ![79507, 43, 43]
    · exact ![103823, 2209]
    · exact ![148877, 53, 53]
    · exact ![59, 59, 59, 59, 59]
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
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
      exact NI59N3
      exact NI59N4
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
  β := ![I29N1, I31N1, I37N1, I43N1, I43N2, I53N1, I53N2, I59N0, I59N1, I59N2, I59N3, I59N4, I61N1, I61N2]
  Il := ![[I29N1], [I31N1], [I37N1], [], [I43N1, I43N2], [], [I53N1, I53N2], [I59N0, I59N1, I59N2, I59N3, I59N4], [I61N1, I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
