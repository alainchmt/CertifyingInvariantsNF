
import IdealArithmetic.Examples.NF5_1_9000000_1.RI5_1_9000000_1
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


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [8, 7, 13, 13, 20, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 24, 5, 1, 3], [26, 14, 28, 17, 3], [26, 5, 3, 11], [9, 14, 22, 0, 23], [0, 1]]
 g := ![![[21, 21, 12, 24, 20], [7, 3, 7, 5], [10, 9, 1], []], ![[22, 0, 21, 26, 20, 13, 8, 21], [1, 11, 6, 6], [25, 19, 17, 1, 20, 10, 20, 18], [6, 16, 22, 25, 7, 19, 9, 27]], ![[26, 22, 13, 20, 16, 12, 17, 8], [8, 2, 21, 28], [26, 24, 25, 21, 22, 9, 18, 11], [18, 10, 19, 7, 22, 15, 6, 27]], ![[22, 23, 21, 5, 9, 17, 27], [18, 26, 27, 24], [5, 15, 6, 23, 28, 16, 26], [0, 18, 22, 18, 26]], ![[0, 18, 16, 20, 21, 23, 5, 20], [19, 19, 26, 7], [22, 13, 13, 5, 0, 9, 25, 23], [16, 13, 26, 26, 13, 13, 28, 16]]]
 h' := ![![[6, 24, 5, 1, 3], [22, 27, 14, 7, 22], [7, 3, 2, 7, 18], [0, 0, 0, 1], [0, 1]], ![[26, 14, 28, 17, 3], [16, 16, 19, 27, 6], [16, 8, 2, 3, 21], [23, 15, 15, 9, 8], [6, 24, 5, 1, 3]], ![[26, 5, 3, 11], [3, 11, 28, 2, 15], [26, 20, 24, 23, 12], [3, 27, 15, 2, 9], [26, 14, 28, 17, 3]], ![[9, 14, 22, 0, 23], [8, 9, 20, 19, 19], [6, 2, 25, 5, 13], [2, 20, 18, 26, 11], [26, 5, 3, 11]], ![[0, 1], [0, 24, 6, 3, 25], [23, 25, 5, 20, 23], [21, 25, 10, 20, 1], [9, 14, 22, 0, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 21, 1, 3], [], [], []]
 b := ![[], [18, 5, 1, 9, 28], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [8, 7, 13, 13, 20, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-324852200, 150196597, 84212143, 73811960, -93651121]
  a := ![0, -7, 2, -8, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11201800, 5179193, 2903867, 2545240, -3229349]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 5 2 4 [23, 15, 21, 16, 6, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 5, 3, 12], [13, 19, 14, 9, 3], [18, 26, 27, 4, 4], [7, 11, 18, 6, 24], [0, 1]]
 g := ![![[10, 24, 0, 17, 20], [20, 21, 22, 26, 10], [20, 25, 1], []], ![[20, 15, 8, 16, 19, 29, 13], [30, 24, 24, 12, 14, 12, 15], [23, 21, 10, 24, 14, 15, 30], [2, 16, 4, 11, 23]], ![[28, 24, 23, 1, 0, 2, 25, 13], [7, 23, 8, 3, 30, 12, 26, 6], [25, 12, 27, 4, 26, 2, 19, 12], [27, 27, 3, 15, 17, 3, 19, 27]], ![[10, 10, 24, 1, 14, 0, 22, 16], [28, 19, 7, 24, 11, 26, 21, 1], [15, 13, 3, 24, 10, 20, 28, 9], [2, 5, 29, 0, 28, 4, 25, 2]], ![[30, 6, 4, 0, 29, 16, 5, 17], [25, 30, 17, 5, 26, 20, 29, 13], [13, 25, 23, 12, 3, 1, 23, 22], [12, 2, 11, 8, 29, 30, 26, 29]]]
 h' := ![![[18, 5, 3, 12], [5, 17, 22, 7, 12], [5, 24, 19, 8, 17], [0, 0, 0, 1], [0, 1]], ![[13, 19, 14, 9, 3], [20, 4, 15, 14, 18], [6, 11, 25, 8, 28], [20, 29, 17, 18, 7], [18, 5, 3, 12]], ![[18, 26, 27, 4, 4], [15, 16, 23, 2, 26], [29, 14, 12, 12, 23], [26, 20, 17, 29, 29], [13, 19, 14, 9, 3]], ![[7, 11, 18, 6, 24], [16, 5, 4, 13, 29], [4, 13, 22, 9, 15], [20, 17, 26, 19, 17], [18, 26, 27, 4, 4]], ![[0, 1], [14, 20, 29, 26, 8], [0, 0, 15, 25, 10], [5, 27, 2, 26, 9], [7, 11, 18, 6, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 20, 25], [], [], []]
 b := ![[], [26, 24, 3, 18, 16], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 5
  hpos := by decide
  P := [23, 15, 21, 16, 6, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2434585094674, 1068517294451, 541532051443, -386533844421, -2323117633159]
  a := ![3, -62, -1, -63, -119]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-78535003054, 34468299821, 17468775853, -12468833691, -74939278489]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 28629151 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀

instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 5 2 5 [24, 16, 30, 9, 5, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 32, 28, 5, 3], [6, 8, 21, 10, 18], [17, 26, 16, 13, 5], [6, 7, 9, 9, 11], [0, 1]]
 g := ![![[23, 28, 36, 14, 7], [34, 0, 32, 27], [19, 9, 16, 32, 1], [], []], ![[29, 24, 15, 20, 3, 31, 25, 11], [34, 21, 10, 30], [22, 9, 0, 25, 22, 4, 3, 9], [6, 30, 15, 9], [31, 2, 22, 9]], ![[7, 22, 7, 14, 4, 36, 7, 14], [23, 1, 24, 36], [20, 15, 1, 33, 17, 13, 19, 24], [34, 21, 33, 28], [35, 22, 35, 28]], ![[35, 30, 1, 34, 10, 8, 32, 32], [21, 22, 16, 4], [8, 13, 29, 13, 26, 13, 22, 20], [1, 32, 17, 36], [4, 5, 5, 25]], ![[7, 25, 1, 4, 17, 7, 9, 1], [21, 12, 35, 30], [33, 20, 35, 22, 36, 11, 2, 3], [0, 29, 23, 3], [33, 4, 0, 10]]]
 h' := ![![[3, 32, 28, 5, 3], [31, 22, 0, 13, 9], [25, 35, 12, 15, 29], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[6, 8, 21, 10, 18], [7, 7, 25, 0, 33], [34, 3, 15, 33, 17], [29, 30, 24, 9, 15], [5, 18, 35, 27, 34], [3, 32, 28, 5, 3]], ![[17, 26, 16, 13, 5], [0, 36, 13, 8, 34], [16, 18, 13, 17, 6], [24, 17, 7, 1, 10], [10, 7, 35, 25, 19], [6, 8, 21, 10, 18]], ![[6, 7, 9, 9, 11], [18, 15, 32, 25, 6], [35, 30, 5, 9, 2], [3, 19, 28, 22, 2], [8, 34, 12, 1, 6], [17, 26, 16, 13, 5]], ![[0, 1], [18, 31, 4, 28, 29], [2, 25, 29, 0, 20], [34, 8, 15, 5, 9], [21, 15, 28, 21, 15], [6, 7, 9, 9, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 8, 22, 18], [], [], []]
 b := ![[], [22, 15, 0, 22, 31], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 5
  hpos := by decide
  P := [24, 16, 30, 9, 5, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-46009019, 19260313, 9913040, -15866377, -59682591]
  a := ![1, -6, 1, -7, -12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1243487, 520549, 267920, -428821, -1613043]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 69343957 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47, 44, -16, 14, 6]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-47, 44, -16, 14, 6]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![27, 14, 1, 0, 0], ![32, 23, 0, 1, 0], ![10, 32, 0, 0, 1]] where
  M :=![![![-47, 44, -16, 14, 6], ![24, -53, 60, -16, 72], ![144, -82, -37, -28, -120], ![-252, 232, -84, 63, 0], ![124, -122, 52, -32, -1]]]
  hmulB := by decide  
  f := ![![![29369, 12768, 9040, 6174, 10710]], ![![42840, 18627, 13188, 9008, 15624]], ![![34731, 15100, 10691, 7302, 12666]], ![![46988, 20429, 14464, 9879, 17136]], ![![40502, 17610, 12468, 8516, 14771]]]
  g := ![![![-3, -6, -16, 14, 6], ![-44, -69, 60, -16, 72], ![79, 120, -37, -28, -120], ![0, -1, -84, 63, 0], ![-6, -2, 52, -32, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [25, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 40], [0, 1]]
 g := ![![[6, 23], [2], [5], [35, 32], [1]], ![[0, 18], [2], [5], [32, 9], [1]]]
 h' := ![![[14, 40], [30, 33], [30, 24], [27, 28], [16, 14], [0, 1]], ![[0, 1], [0, 8], [38, 17], [9, 13], [7, 27], [14, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [1, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [25, 27, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2855, 855, 3547, 5074, 6545]
  a := ![1, 25, -3, 24, 59]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7962, -9145, 3547, 5074, 6545]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73629, -32006, -22664, -15478, -26852]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-73629, -32006, -22664, -15478, -26852]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![25, 19, 1, 0, 0], ![17, 21, 0, 1, 0], ![19, 13, 0, 0, 1]] where
  M :=![![![-73629, -32006, -22664, -15478, -26852], ![-107408, -46693, -33056, -22580, -39164], ![-78328, -34066, -24113, -16472, -28576], ![-3448, -1482, -1066, -719, -1258], ![10004, 4340, 3082, 2100, 3649]]]
  hmulB := by decide  
  f := ![![![-973, 442, 276, 298, -152]], ![![-608, 355, 288, 1452, 2092]], ![![-773, 389, 275, 846, 932]], ![![-597, 307, 222, 759, 902]], ![![-715, 349, 238, 606, 557]]]
  g := ![![![30885, 26164, -22664, -15478, -26852], ![45048, 38163, -33056, -22580, -39164], ![32865, 27841, -24113, -16472, -28576], ![1447, 1225, -1066, -719, -1258], ![-4197, -3555, 3082, 2100, 3649]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [4, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 40], [0, 1]]
 g := ![![[11, 31], [21], [39], [38, 9], [1]], ![[0, 10], [21], [39], [11, 32], [1]]]
 h' := ![![[38, 40], [19, 20], [29, 29], [12, 30], [37, 38], [0, 1]], ![[0, 1], [0, 21], [24, 12], [4, 11], [5, 3], [38, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [18, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [4, 3, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2210, -1564, 264, 494, 1692]
  a := ![-1, -7, 5, -5, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1096, -950, 264, 494, 1692]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27, 10, 4, -32, -74]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-27, 10, 4, -32, -74]] 
 ![![41, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![-27, 10, 4, -32, -74], ![-296, 135, 84, 92, -44], ![-88, 52, 43, 220, 320], ![788, -350, -210, -103, 362], ![48, -30, -26, -148, -223]]]
  hmulB := by decide  
  f := ![![![389, -138, -120, -32, -326]], ![![120, -25, -52, -4, -116]], ![![364, -148, -85, -36, -272]], ![![348, -130, -110, -31, -298]], ![![164, -54, -50, -12, -135]]]
  g := ![![![53, 10, 4, -32, -74], ![-184, 135, 84, 92, -44], ![-388, 52, 43, 220, 320], ![244, -350, -210, -103, 362], ![260, -30, -26, -148, -223]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-47, 44, -16, 14, 6]] ![![-73629, -32006, -22664, -15478, -26852]]
  ![![-389, 138, 120, 32, 326]] where
 M := ![![![-389, 138, 120, 32, 326]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![-389, 138, 120, 32, 326]] ![![-27, 10, 4, -32, -74]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![-41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 5 2 5 [28, 13, 19, 11, 23, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 8, 27, 26, 23], [5, 24, 1, 18, 29], [11, 35, 20, 14, 7], [24, 18, 38, 28, 27], [0, 1]]
 g := ![![[13, 12, 39, 26, 9], [41, 0, 4, 30, 31], [34, 4, 35, 13], [1], []], ![[16, 40, 6, 1, 28, 32, 28, 35], [26, 8, 26, 1, 33, 26, 30, 1], [38, 15, 37, 16], [11, 11, 26, 13, 39, 33, 14, 35], [33, 21, 37, 13]], ![[1, 30, 25, 37, 36, 20, 40, 5], [23, 38, 25, 34, 38, 30, 1, 2], [14, 27, 1, 14], [18, 41, 22, 33, 27, 30, 9, 26], [16, 25, 19, 24]], ![[15, 32, 29, 28, 3, 19, 37, 37], [15, 3, 5, 29, 42, 17, 11, 28], [29, 26, 2, 25], [22, 37, 5, 7, 28, 15, 20, 37], [7, 22, 15, 6]], ![[27, 30, 37, 6, 20, 26], [21, 38, 34, 30, 36, 42, 11, 7], [7, 36, 5, 24], [23, 14, 21, 25, 20, 19, 37, 22], [32, 5, 10, 41]]]
 h' := ![![[23, 8, 27, 26, 23], [13, 42, 28, 3, 3], [4, 2, 28, 13, 17], [15, 30, 24, 32, 20], [0, 0, 1], [0, 1]], ![[5, 24, 1, 18, 29], [1, 18, 21, 14, 3], [20, 28, 34, 42, 12], [3, 28, 7, 13, 4], [35, 39, 15, 21, 40], [23, 8, 27, 26, 23]], ![[11, 35, 20, 14, 7], [38, 8, 13, 9, 31], [39, 28, 39, 10, 36], [42, 33, 9, 14, 10], [7, 20, 27, 34, 11], [5, 24, 1, 18, 29]], ![[24, 18, 38, 28, 27], [23, 12, 22, 23, 6], [3, 27, 22, 17, 41], [27, 13, 10, 24, 38], [11, 20, 9, 33, 37], [11, 35, 20, 14, 7]], ![[0, 1], [28, 6, 2, 37], [30, 1, 6, 4, 23], [22, 25, 36, 3, 14], [24, 7, 34, 41, 41], [24, 18, 38, 28, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 15, 20, 22], [], [], []]
 b := ![[], [9, 10, 18, 23, 14], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 5
  hpos := by decide
  P := [28, 13, 19, 11, 23, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12368055428, 5787301544, 2630534890, -3859554698, -9625506570]
  a := ![0, -4, -2, -14, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-287629196, 134588408, 61175230, -89757086, -223848990]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 147008443 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

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


def P47P0 : CertificateIrreducibleZModOfList' 47 5 2 5 [24, 2, 12, 17, 22, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 13, 32, 45, 25], [7, 43, 4, 12, 45], [29, 41, 26, 6, 36], [40, 43, 32, 31, 35], [0, 1]]
 g := ![![[8, 37, 40, 0, 28], [40, 29, 38, 46, 25], [33, 41, 17, 17, 14], [1], []], ![[9, 40, 19, 8, 13, 43, 11, 37], [21, 18, 44, 21, 18, 18, 30, 3], [14, 1, 24, 6, 42, 42, 36, 12], [45, 14, 40, 27, 28, 6, 19, 21], [8, 2, 15, 14]], ![[13, 40, 13, 7, 16, 16, 19, 31], [13, 2, 43, 37, 7, 34, 11, 41], [17, 31, 28, 14, 33, 25, 9, 45], [9, 1, 44, 38, 3, 44, 34, 38], [45, 44, 5, 4]], ![[6, 21, 3, 11, 46, 30, 22, 42], [34, 2, 33, 33, 29, 8, 10, 21], [15, 9, 10, 5, 9, 45, 43, 3], [5, 31, 41, 46, 24, 22, 34, 32], [30, 31, 26, 27]], ![[30, 13, 34, 45, 15, 25, 28, 29], [27, 31, 14, 35, 21, 4, 39, 44], [31, 7, 3, 23, 45, 31, 45, 23], [37, 10, 26, 38, 27, 23, 1, 46], [34, 8, 36, 3]]]
 h' := ![![[43, 13, 32, 45, 25], [27, 25, 45, 2, 13], [7, 43, 9, 25, 42], [23, 45, 35, 30, 25], [0, 0, 1], [0, 1]], ![[7, 43, 4, 12, 45], [35, 21, 16, 31, 3], [26, 41, 14, 7, 7], [36, 43, 25, 12, 14], [12, 20, 17, 40, 25], [43, 13, 32, 45, 25]], ![[29, 41, 26, 6, 36], [18, 15, 3, 15, 33], [36, 21, 14, 31, 35], [35, 10, 11, 0, 46], [3, 20, 29, 6, 13], [7, 43, 4, 12, 45]], ![[40, 43, 32, 31, 35], [29, 27, 7, 5, 3], [9, 13, 24, 29, 34], [12, 11, 25, 44, 2], [27, 23, 28, 5, 11], [29, 41, 26, 6, 36]], ![[0, 1], [21, 6, 23, 41, 42], [19, 23, 33, 2, 23], [28, 32, 45, 8, 7], [32, 31, 19, 43, 45], [40, 43, 32, 31, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 23, 38], [], [], []]
 b := ![[], [37, 22, 15, 6], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 5
  hpos := by decide
  P := [24, 2, 12, 17, 22, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-153770370, -8551086, 228482228, 256971278, 651978642]
  a := ![13, -7, 4, -6, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3271710, -181938, 4861324, 5467474, 13871886]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![259, -128, -89, -250, -255]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![259, -128, -89, -250, -255]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![31, 8, 1, 0, 0], ![17, 5, 0, 1, 0], ![6, 35, 0, 0, 1]] where
  M :=![![![259, -128, -89, -250, -255], ![-1020, 435, 244, -168, -990], ![-1980, 929, 603, 1066, 486], ![1482, -569, -259, 1267, 3207], ![1324, -623, -406, -744, -379]]]
  hmulB := by decide  
  f := ![![![527, -350, 59, -96, -177]], ![![-708, 925, -508, 280, -222]], ![![193, -65, -30, -14, -117]], ![![149, -62, -24, -15, -96]], ![![-434, 592, -332, 180, -157]]]
  g := ![![![166, 203, -89, -250, -255], ![4, 641, 244, -168, -990], ![-787, -495, 603, 1066, 486], ![-590, -2209, -259, 1267, 3207], ![544, 370, -406, -744, -379]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [52, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 52], [0, 1]]
 g := ![![[16, 52], [52], [2, 40], [11], [16, 1]], ![[0, 1], [52], [6, 13], [11], [32, 52]]]
 h' := ![![[16, 52], [3, 23], [2, 23], [2, 26], [16, 45], [0, 1]], ![[0, 1], [0, 30], [52, 30], [47, 27], [47, 8], [16, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [18, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [52, 37, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![220, -137, -85, -144, 27]
  a := ![-1, -1, -1, -2, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![97, 6, -85, -144, 27]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-159, 83, 61, 222, 275]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-159, 83, 61, 222, 275]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![37, 36, 1, 0, 0], ![46, 48, 0, 1, 0], ![41, 11, 0, 0, 1]] where
  M :=![![![-159, 83, 61, 222, 275], ![1100, -479, -278, 16, 782], ![1564, -746, -495, -1044, -734], ![-2018, 831, 437, -813, -2789], ![-1032, 494, 330, 722, 541]]]
  hmulB := by decide  
  f := ![![![9349, 4037, 2887, 1956, 3413]], ![![13652, 5909, 4162, 2860, 4910]], ![![15985, 6915, 4900, 3348, 5787]], ![![20488, 8857, 6279, 4289, 7413]], ![![10041, 4340, 3089, 2102, 3650]]]
  g := ![![![-451, -298, 61, 222, 275], ![-404, 3, -278, 16, 782], ![1849, 1420, -495, -1044, -734], ![2520, 1034, 437, -813, -2789], ![-1295, -981, 330, 722, 541]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [11, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 52], [0, 1]]
 g := ![![[15, 29], [28], [50, 40], [42], [47, 1]], ![[0, 24], [28], [22, 13], [42], [41, 52]]]
 h' := ![![[47, 52], [39, 33], [33, 44], [25, 27], [13, 25], [0, 1]], ![[0, 1], [0, 20], [34, 9], [22, 26], [22, 28], [47, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [14, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [11, 6, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2726, -1447, -538, -451, -267]
  a := ![3, 3, 0, -1, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1025, 802, -538, -451, -267]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18561, 8069, 5713, 3902, 6769]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![18561, 8069, 5713, 3902, 6769]] 
 ![![53, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![50, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![18561, 8069, 5713, 3902, 6769], ![27076, 11771, 8334, 5692, 9874], ![19748, 8586, 6079, 4152, 7202], ![866, 377, 267, 183, 317], ![-2520, -1096, -776, -530, -919]]]
  hmulB := by decide  
  f := ![![![-67, 151, -165, 44, -149]], ![![-34, 57, -52, 16, -40]], ![![-42, 124, -151, 36, -148]], ![![-32, 67, -71, 21, -65]], ![![-45, 103, -113, 30, -100]]]
  g := ![![![-14086, 8069, 5713, 3902, 6769], ![-20548, 11771, 8334, 5692, 9874], ![-14988, 8586, 6079, 4152, 7202], ![-659, 377, 267, 183, 317], ![1913, -1096, -776, -530, -919]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![259, -128, -89, -250, -255]] ![![-159, 83, 61, 222, 275]]
  ![![446483, -184517, -97962, 167506, 595750]] where
 M := ![![![446483, -184517, -97962, 167506, 595750]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![446483, -184517, -97962, 167506, 595750]] ![![18561, 8069, 5713, 3902, 6769]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![405291, -172250, -96195, 73776, 405397]]]
 hmul := by decide  
 g := ![![![![7647, -3250, -1815, 1392, 7649]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 5 2 5 [48, 42, 48, 38, 24, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 21, 5, 32, 19], [3, 14, 9, 53, 11], [17, 6, 2, 49, 42], [10, 17, 43, 43, 46], [0, 1]]
 g := ![![[38, 34, 57, 6, 51], [32, 54, 9, 48, 28], [19, 28, 6, 26], [7, 35, 1], []], ![[23, 18, 20, 12, 9, 24, 32, 20], [15, 33, 11, 21, 41, 49, 8, 35], [20, 21, 7, 9], [24, 58, 0, 4, 27, 54, 7, 27], [11, 12, 6, 53, 4, 29, 17, 15]], ![[38, 54, 23, 30, 17, 33, 55, 39], [32, 22, 48, 3, 52, 42, 0, 2], [21, 29], [22, 2, 2, 16, 39, 17, 2, 43], [11, 38, 55, 20, 44, 23, 39, 33]], ![[9, 53, 10, 58, 50, 25, 6, 13], [1, 45, 38, 20, 35, 37, 24, 24], [58, 4, 49, 46], [10, 49, 31, 22, 12, 1, 0, 54], [18, 57, 58, 11, 37, 49, 33, 43]], ![[2, 30, 25, 16, 54, 16, 49, 3], [11, 25, 23, 50, 9, 24, 57, 7], [7, 18, 12, 3], [1, 53, 57, 18, 3, 57, 56, 5], [2, 12, 22, 3, 42, 25, 12, 45]]]
 h' := ![![[5, 21, 5, 32, 19], [57, 21, 5, 11, 13], [2, 13, 49, 25, 38], [18, 32, 34, 18, 47], [0, 0, 0, 1], [0, 1]], ![[3, 14, 9, 53, 11], [56, 53, 21, 22, 41], [52, 43, 46, 21, 53], [56, 29, 35, 47, 3], [10, 6, 6, 47, 15], [5, 21, 5, 32, 19]], ![[17, 6, 2, 49, 42], [57, 19, 9, 27, 5], [0, 23, 9, 8, 26], [51, 15, 44, 41], [30, 39, 16, 46, 43], [3, 14, 9, 53, 11]], ![[10, 17, 43, 43, 46], [47, 2, 9, 2, 33], [55, 14, 22, 21, 3], [19, 54, 51, 48, 20], [37, 58, 6, 15, 25], [17, 6, 2, 49, 42]], ![[0, 1], [35, 23, 15, 56, 26], [30, 25, 51, 43, 57], [22, 47, 13, 23, 48], [19, 15, 31, 9, 35], [10, 17, 43, 43, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 8, 26, 23], [], [], []]
 b := ![[], [58, 53, 2, 45, 5], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 5
  hpos := by decide
  P := [48, 42, 48, 38, 24, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-307943951, 131170629, 87975077, 39830192, -155621999]
  a := ![1, 5, -3, 4, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5219389, 2223231, 1491103, 675088, -2637661]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 714924299 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45, 48, -25, 14, -7]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-45, 48, -25, 14, -7]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![54, 59, 1, 0, 0], ![47, 54, 0, 1, 0], ![47, 56, 0, 0, 1]] where
  M :=![![![-45, 48, -25, 14, -7], ![-28, -21, 68, -8, 98], ![196, -135, -13, -38, -122], ![-230, 247, -131, 75, -41], ![124, -135, 74, -40, 29]]]
  hmulB := by decide  
  f := ![![![1271, 546, 387, 264, 463]], ![![1852, 797, 564, 376, 658]], ![![2938, 1264, 895, 602, 1054]], ![![2619, 1127, 798, 537, 940]], ![![2677, 1151, 815, 548, 960]]]
  g := ![![![16, 19, -25, 14, -7], ![-130, -149, 68, -8, 98], ![138, 156, -13, -38, -122], ![86, 102, -131, 75, -41], ![-55, -65, 74, -40, 29]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [21, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 60], [0, 1]]
 g := ![![[59, 58], [16], [18, 47], [19, 5], [42, 1]], ![[55, 3], [16], [40, 14], [46, 56], [23, 60]]]
 h' := ![![[42, 60], [52, 27], [49, 4], [28, 13], [33, 35], [0, 1]], ![[0, 1], [27, 34], [34, 57], [25, 48], [39, 26], [42, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [29, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [21, 19, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![209, -49, -28, -4, -132]
  a := ![4, 0, 0, 1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![133, 151, -28, -4, -132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![93, 41, 29, 20, 35]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![93, 41, 29, 20, 35]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![12, 28, 1, 0, 0], ![30, 46, 0, 1, 0], ![54, 58, 0, 0, 1]] where
  M :=![![![93, 41, 29, 20, 35], ![140, 57, 42, 28, 50], ![100, 44, 29, 20, 34], ![-2, 5, 3, 1, 1], ![-12, -6, -4, -2, -5]]]
  hmulB := by decide  
  f := ![![![-7, 3, 3, -2, 1]], ![![4, -11, 10, 0, -14]], ![![0, -4, 5, 0, -6]], ![![0, -7, 9, -1, -9]], ![![-2, -8, 12, -2, -13]]]
  g := ![![![-45, -61, 29, 20, 35], ![-64, -87, 42, 28, 50], ![-44, -60, 29, 20, 34], ![-2, -3, 3, 1, 1], ![6, 8, -4, -2, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [60, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 60], [0, 1]]
 g := ![![[8, 60], [39], [54, 46], [9, 16], [8, 1]], ![[0, 1], [39], [56, 15], [15, 45], [16, 60]]]
 h' := ![![[8, 60], [27, 50], [54, 10], [9, 30], [8, 4], [0, 1]], ![[0, 1], [0, 11], [12, 51], [5, 31], [40, 57], [8, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [36, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [60, 53, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![984, -2976, 2444, 2564, -648]
  a := ![7, -21, -1, -21, -65]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1152, -2488, 2444, 2564, -648]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 3, 2, 0, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![7, 3, 2, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![51, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![7, 3, 2, 0, 0], ![0, 9, 6, 4, 0], ![0, 7, 5, 10, 12], ![24, -10, -6, 1, 18], ![4, -3, -2, -6, -7]]]
  hmulB := by decide  
  f := ![![![91, -97, 56, -28, 24]], ![![15, -14, 6, -4, 0]], ![![69, -76, 47, -22, 24]], ![![22, -24, 14, -7, 6]], ![![20, -21, 12, -6, 5]]]
  g := ![![![-2, 3, 2, 0, 0], ![-7, 9, 6, 4, 0], ![-10, 7, 5, 10, 12], ![2, -10, -6, 1, 18], ![5, -3, -2, -6, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-45, 48, -25, 14, -7]] ![![93, 41, 29, 20, 35]]
  ![![91, -97, 56, -28, 24]] where
 M := ![![![91, -97, 56, -28, 24]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![91, -97, 56, -28, 24]] ![![7, 3, 2, 0, 0]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![61, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB187I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB187I1 : PrimesBelowBoundCertificateInterval O 23 61 187 where
  m := 9
  g := ![1, 1, 1, 3, 1, 1, 3, 1, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB187I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0]
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0]
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
    · exact ![20511149]
    · exact ![28629151]
    · exact ![69343957]
    · exact ![1681, 1681, 41]
    · exact ![147008443]
    · exact ![229345007]
    · exact ![2809, 2809, 53]
    · exact ![714924299]
    · exact ![3721, 3721, 61]
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
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
  β := ![I41N2, I53N2, I61N2]
  Il := ![[], [], [], [I41N2], [], [], [I53N2], [], [I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
