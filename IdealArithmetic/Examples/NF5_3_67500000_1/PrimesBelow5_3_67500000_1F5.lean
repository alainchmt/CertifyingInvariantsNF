
import IdealArithmetic.Examples.NF5_3_67500000_1.RI5_3_67500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0, 0, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0, 0, 0]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![0, 0, 199, 0, 0], ![0, 0, 0, 199, 0], ![0, 0, 0, 0, 199]] where
  M :=![![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![0, 0, 199, 0, 0], ![0, 0, 0, 199, 0], ![0, 0, 0, 0, 199]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 5 2 7 [141, 97, 60, 133, 85, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [126, 1, 161, 39, 129], [45, 26, 153, 93, 37], [100, 19, 48, 50, 78], [42, 152, 36, 17, 154], [0, 1]]
 g := ![![[160, 20, 10, 60, 178], [74, 68, 165, 134, 172], [130, 7, 61, 4, 80], [129, 38, 42, 175], [196, 128, 128, 10], [114, 1], []], ![[44, 197, 129, 59, 83, 125, 63, 60], [3, 195, 48, 122, 88, 76, 27, 11], [45, 2, 122, 111, 98, 155, 39, 109], [98, 148, 33, 160], [25, 168, 154, 112], [84, 145, 122, 23], [14, 20, 18, 81, 184, 101, 88, 76]], ![[75, 182, 126, 21, 143, 129, 8, 74], [88, 100, 99, 188, 150, 48, 83, 88], [8, 60, 157, 95, 63, 166, 42, 68], [86, 188, 137, 80], [25, 34, 106, 29], [74, 163, 190, 187], [22, 161, 170, 168, 39, 69, 129, 107]], ![[116, 180, 9, 131, 0, 146, 43, 84], [76, 107, 52, 139, 20, 166, 6, 15], [85, 184, 133, 26, 138, 123, 146, 147], [170, 24, 171, 29], [165, 16, 8, 172], [157, 102, 198, 158], [63, 26, 46, 89, 77, 192, 167, 136]], ![[117, 104, 146, 195, 198, 79, 104, 44], [22, 193, 66, 75, 154, 9, 93, 171], [5, 139, 134, 156, 116, 123, 23, 154], [153, 34, 150, 43], [175, 124, 134, 7], [62, 191, 11, 16], [172, 169, 65, 160, 55, 70, 141, 17]]]
 h' := ![![[126, 1, 161, 39, 129], [113, 36, 15, 76, 24], [177, 197, 24, 133, 42], [137, 106, 10, 87, 94], [60, 178, 136, 27, 162], [45, 144, 28, 101, 127], [0, 0, 0, 1], [0, 1]], ![[45, 26, 153, 93, 37], [28, 147, 65, 174, 102], [20, 96, 181, 162, 14], [17, 50, 113, 161, 48], [30, 56, 119, 71, 89], [42, 77, 79, 154, 149], [44, 68, 76, 44, 53], [126, 1, 161, 39, 129]], ![[100, 19, 48, 50, 78], [81, 48, 45, 116, 20], [98, 97, 140, 32, 185], [59, 145, 182, 118, 85], [65, 185, 82, 93, 94], [159, 196, 108, 50, 167], [65, 183, 151, 106, 28], [45, 26, 153, 93, 37]], ![[42, 152, 36, 17, 154], [110, 115, 26, 48, 131], [110, 22, 154, 66, 151], [67, 194, 187, 28, 172], [82, 35, 29, 178, 32], [8, 49, 41, 32, 42], [97, 38, 28, 95, 122], [100, 19, 48, 50, 78]], ![[0, 1], [3, 52, 48, 183, 121], [44, 185, 98, 5, 6], [161, 102, 105, 4, 198], [21, 143, 32, 29, 21], [47, 131, 142, 61, 112], [86, 109, 143, 152, 195], [42, 152, 36, 17, 154]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [112, 125, 194, 103], [], [], []]
 b := ![[], [110, 164, 104, 159, 10], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 5
  hpos := by decide
  P := [141, 97, 60, 133, 85, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-96456295, -75051059, 13218973, -26797738, -242888654]
  a := ![-5, -7, 2, -8, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-484705, -377141, 66427, -134662, -1220546]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 312079600999 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def PBC199 : ContainsPrimesAboveP 199 ![I199N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![199, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 199 (by decide) 𝕀

instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-239, -456, 28, 338, 426]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![-239, -456, 28, 338, 426]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![21, 132, 27, 1, 0], ![12, 126, 152, 0, 1]] where
  M :=![![![-239, -456, 28, 338, 426], ![-264, -475, 146, 644, 750], ![-318, -436, 487, 1474, 1614], ![-78, 112, 656, 1569, 1626], ![156, 332, 56, -52, -107]]]
  hmulB := by decide  
  f := ![![![-17, 32, -12, 2, 6]], ![![-12, -41, 46, -24, -6]], ![![-54, -20, -11, 26, -126]], ![![-15, -24, 25, -11, -18]], ![![-48, -38, 20, 4, -95]]]
  g := ![![![-59, -468, -350, 338, 426], ![-108, -853, -622, 644, 750], ![-240, -1888, -1349, 1474, 1614], ![-249, -1952, -1369, 1569, 1626], ![12, 98, 84, -52, -107]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [60, 91, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [137, 180, 82], [62, 30, 129], [0, 1]]
 g := ![![[163, 120, 34], [82], [134, 120], [176, 37], [41, 43, 49], [34, 144], [1]], ![[0, 178, 45, 113], [35, 16, 83, 151], [63, 54], [67, 176], [191, 127, 45, 208], [203, 14], [95, 11, 194, 25]], ![[116, 128, 101, 110], [9, 51, 53, 60], [129, 136], [207, 101], [125, 19, 183, 31], [41, 96], [138, 14, 101, 186]]]
 h' := ![![[137, 180, 82], [144, 203, 178], [51, 90], [110, 8, 72], [72, 156, 167], [83, 30, 7], [151, 120, 199], [0, 1]], ![[62, 30, 129], [76, 54, 42], [143, 164, 206], [114, 41, 73], [97, 110, 78], [113, 115, 138], [104, 65, 196], [137, 180, 82]], ![[0, 1], [85, 165, 202], [145, 168, 5], [17, 162, 66], [58, 156, 177], [60, 66, 66], [58, 26, 27], [62, 30, 129]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 9], []]
 b := ![[], [72, 180, 162], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [60, 91, 12, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11996763, -22272340, 33820946, -62401243, -3407904]
  a := ![6, -59, -1, -60, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6347508, 40967240, 10600265, -62401243, -3407904]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, 32, -12, 2, 6]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![-17, 32, -12, 2, 6]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![121, 157, 1, 0, 0], ![102, 80, 0, 1, 0], ![170, 152, 0, 0, 1]] where
  M :=![![![-17, 32, -12, 2, 6], ![-12, -41, 46, -24, -6], ![-54, -20, -11, 26, -126], ![234, 216, -248, 103, 270], ![-204, -196, 240, -108, -209]]]
  hmulB := by decide  
  f := ![![![-239, -456, 28, 338, 426]], ![![-264, -475, 146, 644, 750]], ![![-335, -617, 127, 680, 810]], ![![-216, -400, 72, 415, 498]], ![![-382, -708, 128, 736, 883]]]
  g := ![![![1, 4, -12, 2, 6], ![-10, -21, 46, -24, -6], ![95, 89, -11, 26, -126], ![-124, -48, -248, 103, 270], ![82, 12, 240, -108, -209]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P1 : CertificateIrreducibleZModOfList' 211 2 2 7 [126, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [119, 210], [0, 1]]
 g := ![![[128, 139], [106, 125], [154], [170], [10, 194], [65], [119, 1]], ![[0, 72], [0, 86], [154], [170], [97, 17], [65], [27, 210]]]
 h' := ![![[119, 210], [148, 75], [62, 97], [138, 187], [6, 176], [208, 48], [198, 109], [0, 1]], ![[0, 1], [0, 136], [0, 114], [25, 24], [61, 35], [12, 163], [87, 102], [119, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [118, 131]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N1 : CertifiedPrimeIdeal' SI211N1 211 where
  n := 2
  hpos := by decide
  P := [126, 92, 1]
  hirr := P211P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![239, -214, -74, -68, 183]
  a := ![-1, -5, 1, -6, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-71, -52, -74, -68, 183]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N1 B_one_repr
lemma NI211N1 : Nat.card (O ⧸ I211N1) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![-239, -456, 28, 338, 426]] ![![-17, 32, -12, 2, 6]]
  ![![211, 0, 0, 0, 0]] where
 M := ![![![211, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![186, 258, -362, 197, 76]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![186, 258, -362, 197, 76]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![0, 0, 223, 0, 0], ![0, 0, 0, 223, 0], ![67, 21, 95, 29, 1]] where
  M :=![![![186, 258, -362, 197, 76], ![363, 187, 92, -209, 954], ![-3489, -3034, 3467, -1397, -4116], ![3897, 3974, -6340, 3534, 1506], ![-2372, -2614, 4698, -2824, 141]]]
  hmulB := by decide  
  f := ![![![12, 26, -16, -55, -62]], ![![21, 17, -50, -135, -144]], ![![27, -2, -145, -361, -378]], ![![15, -42, -182, -430, -444]], ![![19, 3, -95, -239, -251]]]
  g := ![![![-22, -6, -34, -9, 76], ![-285, -89, -406, -125, 954], ![1221, 374, 1769, 529, -4116], ![-435, -124, -670, -180, 1506], ![-53, -25, -39, -31, 141]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 4 2 7 [21, 119, 191, 85, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [191, 117, 174, 108], [128, 147, 219, 205], [42, 181, 53, 133], [0, 1]]
 g := ![![[44, 52, 97, 124], [7, 197, 201, 126], [179, 34, 105, 171], [144, 160, 188, 183], [102, 116, 77, 197], [121, 138, 1], []], ![[79, 5, 186, 206, 141, 165], [75, 2, 172, 32, 70, 91], [133, 147, 120, 77, 29, 108], [30, 183, 114, 48, 172, 191], [110, 19, 124, 85, 9, 154], [147, 95, 49], [95, 193, 42, 106, 199, 208]], ![[11, 89, 20, 0, 106, 140], [103, 90, 135, 84, 165, 54], [197, 175, 30, 193, 204, 99], [54, 180, 186, 37, 159, 145], [190, 89, 62, 152, 87, 182], [135, 165, 49], [222, 173, 124, 86, 117, 189]], ![[138, 165, 16, 9, 90, 153], [123, 126, 153, 164, 56, 1], [116, 14, 45, 22, 110, 143], [197, 150, 209, 140, 168, 41], [20, 7, 19, 113, 219, 175], [8, 128, 1], [30, 107, 219, 144, 65, 210]]]
 h' := ![![[191, 117, 174, 108], [76, 68, 11, 149], [32, 77, 138, 168], [98, 182, 19, 174], [88, 83, 207, 184], [135, 97, 140, 33], [0, 0, 0, 1], [0, 1]], ![[128, 147, 219, 205], [176, 62, 173, 211], [193, 212, 215, 33], [196, 190, 111, 1], [4, 198, 83, 189], [214, 101, 149, 25], [25, 200, 145, 7], [191, 117, 174, 108]], ![[42, 181, 53, 133], [140, 142, 134, 169], [133, 108, 80, 144], [15, 181, 152, 38], [49, 95, 192, 162], [158, 58, 121, 138], [81, 198, 73, 216], [128, 147, 219, 205]], ![[0, 1], [192, 174, 128, 140], [159, 49, 13, 101], [167, 116, 164, 10], [196, 70, 187, 134], [85, 190, 36, 27], [91, 48, 5, 222], [42, 181, 53, 133]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [145, 81, 6], []]
 b := ![[], [], [25, 22, 136, 149], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 4
  hpos := by decide
  P := [21, 119, 191, 85, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![174793140, 252388140, 219598116, 867171531, 1184181156]
  a := ![8, 26, -3, 25, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-355001544, -110383032, -503487048, -150107991, 1184181156]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 2472973441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12, -26, 16, 55, 62]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-12, -26, 16, 55, 62]] 
 ![![223, 0, 0, 0, 0], ![52, 1, 0, 0, 0], ![195, 0, 1, 0, 0], ![33, 0, 0, 1, 0], ![183, 0, 0, 0, 1]] where
  M :=![![![-12, -26, 16, 55, 62], ![-21, -17, 50, 135, 144], ![-27, 2, 145, 361, 378], ![-15, 42, 182, 430, 444], ![8, 22, 10, 12, 9]]]
  hmulB := by decide  
  f := ![![![-186, -258, 362, -197, -76]], ![![-45, -61, 84, -45, -22]], ![![-147, -212, 301, -166, -48]], ![![-45, -56, 82, -45, -18]], ![![-142, -200, 276, -149, -63]]]
  g := ![![![-67, -26, 16, 55, 62], ![-178, -17, 50, 135, 144], ![-491, 2, 145, 361, 378], ![-597, 42, 182, 430, 444], ![-23, 22, 10, 12, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![186, 258, -362, 197, 76]] ![![-12, -26, 16, 55, 62]]
  ![![223, 0, 0, 0, 0]] where
 M := ![![![-223, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![398, 111, -61, -237, -246]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![398, 111, -61, -237, -246]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![0, 0, 0, 227, 0], ![218, 30, 51, 120, 1]] where
  M :=![![![398, 111, -61, -237, -246], ![27, 364, -153, -587, -684], ![291, 165, -514, -1383, -1470], ![117, -163, -663, -1560, -1602], ![-153, -171, -41, -3, 17]]]
  hmulB := by decide  
  f := ![![![-2, -3, 5, -3, 0]], ![![-9, -6, 3, 1, -18]], ![![57, 51, -62, 27, 60]], ![![-45, -49, 87, -52, 0]], ![![-14, -18, 37, -24, 11]]]
  g := ![![![238, 33, 55, 129, -246], ![657, 92, 153, 359, -684], ![1413, 195, 328, 771, -1470], ![1539, 211, 357, 840, -1602], ![-17, -3, -4, -9, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 4 2 7 [1, 93, 207, 19, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 103, 210, 105], [176, 226, 81, 80], [225, 124, 163, 42], [0, 1]]
 g := ![![[193, 22, 16, 139], [82, 138, 162, 82], [145, 55, 11], [177, 56, 104], [73, 18, 90], [6, 154, 208, 1], []], ![[38, 122, 83, 147, 172, 220], [44, 42, 139, 85, 159, 168], [167, 83, 175], [137, 148, 4], [136, 78, 173], [162, 162, 214, 32, 125, 105], [159, 162, 90, 95, 67, 152]], ![[143, 200, 186, 159, 222, 72], [11, 57, 219, 205, 63, 118], [115, 74, 212], [177, 198, 16], [171, 6, 113], [105, 6, 131, 143, 49, 88], [86, 89, 192, 57, 108, 115]], ![[53, 193, 119, 26, 113, 80], [201, 132, 217, 127, 118, 165], [27, 65, 10], [36, 26, 85], [152, 107, 104], [206, 50, 35, 115, 160, 200], [30, 226, 169, 3, 178, 86]]]
 h' := ![![[34, 103, 210, 105], [145, 209, 106, 65], [153, 79, 61, 189], [57, 225, 26, 40], [190, 148, 149, 51], [221, 196, 118, 192], [0, 0, 0, 1], [0, 1]], ![[176, 226, 81, 80], [184, 144, 220, 216], [52, 213, 100, 71], [30, 33, 154, 185], [124, 10, 171, 225], [43, 222, 1, 207], [101, 166, 128, 1], [34, 103, 210, 105]], ![[225, 124, 163, 42], [8, 18, 57, 110], [97, 148, 188, 141], [62, 2, 139, 165], [127, 79, 6, 4], [170, 31, 144, 106], [58, 0, 210, 198], [176, 226, 81, 80]], ![[0, 1], [108, 83, 71, 63], [58, 14, 105, 53], [174, 194, 135, 64], [94, 217, 128, 174], [84, 5, 191, 176], [189, 61, 116, 27], [225, 124, 163, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [42, 118, 32], []]
 b := ![[], [], [210, 222, 39, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 4
  hpos := by decide
  P := [1, 93, 207, 19, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21849643, -31185764, 76174532, -51601840, 43601326]
  a := ![-10, -8, 5, -6, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-41968893, -5899672, -9460322, -23276480, 43601326]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 2655237841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -3, 5, -3, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![-2, -3, 5, -3, 0]] 
 ![![227, 0, 0, 0, 0], ![191, 1, 0, 0, 0], ![66, 0, 1, 0, 0], ![71, 0, 0, 1, 0], ![204, 0, 0, 0, 1]] where
  M :=![![![-2, -3, 5, -3, 0], ![-9, -6, 3, 1, -18], ![57, 51, -62, 27, 60], ![-45, -49, 87, -52, 0], ![21, 27, -59, 39, -23]]]
  hmulB := by decide  
  f := ![![![398, 111, -61, -237, -246]], ![![335, 95, -52, -202, -210]], ![![117, 33, -20, -75, -78]], ![![125, 34, -22, -81, -84]], ![![357, 99, -55, -213, -221]]]
  g := ![![![2, -3, 5, -3, 0], ![20, -6, 3, 1, -18], ![-87, 51, -62, 27, 60], ![32, -49, 87, -52, 0], ![3, 27, -59, 39, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![398, 111, -61, -237, -246]] ![![-2, -3, 5, -3, 0]]
  ![![227, 0, 0, 0, 0]] where
 M := ![![![227, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12, -4, -8, 1, -4]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![12, -4, -8, 1, -4]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![0, 0, 229, 0, 0], ![61, 127, 12, 1, 0], ![184, 90, 5, 0, 1]] where
  M :=![![![12, -4, -8, 1, -4], ![15, 19, -18, -9, 18], ![-81, -84, 91, -81, -108], ![33, 36, -114, 28, -90], ![2, -8, 52, -46, 75]]]
  hmulB := by decide  
  f := ![![![78, 124, 10, -49, -70]], ![![63, 151, 12, -57, -84]], ![![81, 156, 13, -63, -90]], ![![60, 125, 10, -48, -70]], ![![89, 162, 13, -63, -91]]]
  g := ![![![3, 1, 0, 1, -4], ![-12, -2, 0, -9, 18], ![108, 87, 7, -81, -108], ![65, 20, 0, 28, -90], ![-48, -4, 1, -46, 75]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [37, 102, 227, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [174, 45, 129], [57, 183, 100], [0, 1]]
 g := ![![[51], [12, 62], [80, 187, 108], [19, 168], [228, 172], [117, 58, 4], [1]], ![[144, 134, 40, 132], [], [123, 119, 127, 169], [178, 214], [172, 99], [76, 222, 180, 192], [39, 209, 131, 43]], ![[43, 93, 138, 97], [114, 62], [78, 225, 201, 214], [95, 138], [217, 169], [159, 105, 131, 184], [98, 69, 97, 186]]]
 h' := ![![[174, 45, 129], [74, 76], [17, 200, 73], [60, 140, 197], [63, 84, 54], [22, 113, 115], [192, 127, 2], [0, 1]], ![[57, 183, 100], [16, 214, 186], [225, 145], [67, 68, 67], [142, 213, 108], [95, 173, 127], [39, 36, 32], [174, 45, 129]], ![[0, 1], [55, 168, 43], [36, 113, 156], [92, 21, 194], [115, 161, 67], [75, 172, 216], [199, 66, 195], [57, 183, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [190, 88], []]
 b := ![[], [82, 15, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [37, 102, 227, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1148953, 921264, -615216, 197484, 2078448]
  a := ![6, -4, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1717607, -922356, -58416, 197484, 2078448]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 12008989 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![78, 124, 10, -49, -70]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![78, 124, 10, -49, -70]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![94, 205, 1, 0, 0], ![212, 103, 0, 1, 0], ![106, 83, 0, 0, 1]] where
  M :=![![![78, 124, 10, -49, -70], ![63, 151, 12, -57, -84], ![81, 156, 13, -63, -90], ![9, 12, 0, -8, -12], ![-46, -88, -8, 34, 51]]]
  hmulB := by decide  
  f := ![![![12, -4, -8, 1, -4]], ![![15, 19, -18, -9, 18]], ![![18, 15, -19, -8, 14]], ![![18, 5, -16, -3, 4]], ![![11, 5, -10, -3, 5]]]
  g := ![![![74, 39, 10, -49, -70], ![87, 46, 12, -57, -84], ![95, 50, 13, -63, -90], ![13, 8, 0, -8, -12], ![-52, -27, -8, 34, 51]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P1 : CertificateIrreducibleZModOfList' 229 2 2 7 [115, 101, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [128, 228], [0, 1]]
 g := ![![[202, 218], [91], [49, 220], [212], [148], [70, 100], [128, 1]], ![[168, 11], [91], [42, 9], [212], [148], [46, 129], [27, 228]]]
 h' := ![![[128, 228], [154, 203], [90, 70], [159, 137], [6, 21], [194, 182], [165, 10], [0, 1]], ![[0, 1], [32, 26], [119, 159], [62, 92], [175, 208], [132, 47], [71, 219], [128, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [42, 121]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N1 : CertifiedPrimeIdeal' SI229N1 229 where
  n := 2
  hpos := by decide
  P := [115, 101, 1]
  hirr := P229P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![350, 552, 1062, 1759, 76]
  a := ![6, 6, 4, 7, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2098, -1767, 1062, 1759, 76]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N1 B_one_repr
lemma NI229N1 : Nat.card (O ⧸ I229N1) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![12, -4, -8, 1, -4]] ![![78, 124, 10, -49, -70]]
  ![![229, 0, 0, 0, 0]] where
 M := ![![![229, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-32, -3, 25, -15, -24]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![-32, -3, 25, -15, -24]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![0, 0, 233, 0, 0], ![36, 2, 188, 1, 0], ![173, 28, 163, 0, 1]] where
  M :=![![![-32, -3, 25, -15, -24], ![27, 20, -45, 29, -18], ![141, 123, -92, 15, 228], ![-333, -305, 411, -198, -288], ![261, 243, -355, 183, 187]]]
  hmulB := by decide  
  f := ![![![-4, 21, 13, 21, 18]], ![![9, 18, 33, 71, 72]], ![![-3, 39, 92, 207, 210]], ![![-3, 35, 77, 172, 174]], ![![-4, 45, 78, 169, 169]]]
  g := ![![![20, 3, 29, -15, -24], ![9, 2, -11, 29, -18], ![-171, -27, -172, 15, 228], ![243, 35, 363, -198, -288], ![-166, -23, -280, 183, 187]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [168, 97, 65, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 230, 29], [77, 2, 204], [0, 1]]
 g := ![![[48, 223, 110], [1, 162], [200, 152], [19, 62, 72], [196, 7], [122, 110, 31], [1]], ![[59, 129, 31, 23], [71, 161], [146, 178], [45, 121, 20, 184], [136, 8], [98, 141, 165, 124], [223, 184, 167, 157]], ![[131, 171, 231, 7], [167, 208], [153, 144], [215, 75, 178, 100], [165, 49], [59, 28, 90, 26], [19, 18, 106, 76]]]
 h' := ![![[91, 230, 29], [115, 26, 209], [192, 215, 167], [70, 211, 131], [222, 195, 189], [8, 7, 163], [65, 136, 168], [0, 1]], ![[77, 2, 204], [17, 209, 7], [166, 86, 45], [178, 179, 90], [91, 213, 208], [60, 20, 63], [98, 146, 86], [91, 230, 29]], ![[0, 1], [105, 231, 17], [30, 165, 21], [77, 76, 12], [209, 58, 69], [193, 206, 7], [156, 184, 212], [77, 2, 204]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97, 87], []]
 b := ![[], [205, 211, 230], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [168, 97, 65, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![38642, 32196, -28307, 10759, 58415]
  a := ![2, -2, -1, -3, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-44869, -6974, -49668, 10759, 58415]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, 4, 0, -1, -2]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![-6, 4, 0, -1, -2]] 
 ![![233, 0, 0, 0, 0], ![104, 1, 0, 0, 0], ![135, 0, 1, 0, 0], ![151, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![-6, 4, 0, -1, -2], ![3, -3, 0, -1, 0], ![-3, 0, -1, -3, -6], ![3, 4, -6, -2, 0], ![-2, -4, 4, -2, -3]]]
  hmulB := by decide  
  f := ![![![-180, -308, -22, 113, 164]], ![![-81, -139, -10, 51, 74]], ![![-105, -180, -13, 66, 96]], ![![-117, -200, -14, 73, 106]], ![![-14, -24, -2, 9, 13]]]
  g := ![![![-1, 4, 0, -1, -2], ![2, -3, 0, -1, 0], ![3, 0, -1, -3, -6], ![3, 4, -6, -2, 0], ![1, -4, 4, -2, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1

def I233N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 35, 5, -8, -14]] i)))

def SI233N2: IdealEqSpanCertificate' Table ![![15, 35, 5, -8, -14]] 
 ![![233, 0, 0, 0, 0], ![219, 1, 0, 0, 0], ![37, 0, 1, 0, 0], ![33, 0, 0, 1, 0], ![158, 0, 0, 0, 1]] where
  M :=![![![15, 35, 5, -8, -14], ![18, 38, 9, 0, -6], ![18, 45, 20, 24, 18], ![0, 9, 21, 47, 48], ![-11, -23, -1, 11, 15]]]
  hmulB := by decide  
  f := ![![![-111, 83, 31, -38, 14]], ![![-105, 77, 30, -36, 12]], ![![-15, 16, 1, -4, 4]], ![![-15, 12, 6, -7, 6]], ![![-77, 55, 21, -25, 5]]]
  g := ![![![-23, 35, 5, -8, -14], ![-33, 38, 9, 0, -6], ![-61, 45, 20, 24, 18], ![-51, 9, 21, 47, 48], ![10, -23, -1, 11, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N2 : Nat.card (O ⧸ I233N2) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N2)

lemma isPrimeI233N2 : Ideal.IsPrime I233N2 := prime_ideal_of_norm_prime hp233.out _ NI233N2
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![-32, -3, 25, -15, -24]] ![![-6, 4, 0, -1, -2]]
  ![![111, -83, -31, 38, -14]] where
 M := ![![![111, -83, -31, 38, -14]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI233N1 : IdealMulLeCertificate' Table 
  ![![111, -83, -31, 38, -14]] ![![15, 35, 5, -8, -14]]
  ![![233, 0, 0, 0, 0]] where
 M := ![![![-233, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1, I233N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
    exact isPrimeI233N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0 ⊙ MulI233N1)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-61, 126, -62, 20, 6]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![-61, 126, -62, 20, 6]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![101, 206, 1, 0, 0], ![113, 104, 0, 1, 0], ![139, 130, 0, 0, 1]] where
  M :=![![![-61, 126, -62, 20, 6], ![42, -81, 104, -70, 102], ![-516, -370, 365, -104, -726], ![912, 898, -1222, 607, 726], ![-678, -706, 1022, -538, -415]]]
  hmulB := by decide  
  f := ![![![-947, 3462, 13226, 31004, 31938]], ![![-2802, 9477, 37268, 87526, 90210]], ![![-2849, 9742, 38151, 89576, 92316]], ![![-1709, 5896, 23012, 54019, 55668]], ![![-2077, 7174, 27988, 65698, 67703]]]
  g := ![![![13, 42, -62, 20, 6], ![-70, -115, 104, -70, 102], ![315, 124, 365, -104, -726], ![-189, 398, -1222, 607, 726], ![61, -424, 1022, -538, -415]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [27, 148, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 238], [0, 1]]
 g := ![![[94, 62], [98, 34], [152, 80], [109, 9], [153], [118, 132], [91, 1]], ![[0, 177], [85, 205], [23, 159], [211, 230], [153], [180, 107], [182, 238]]]
 h' := ![![[91, 238], [222, 121], [198, 89], [164, 124], [198, 236], [160, 191], [172, 128], [0, 1]], ![[0, 1], [0, 118], [171, 150], [215, 115], [164, 3], [94, 48], [109, 111], [91, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [185, 122]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [27, 148, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-849, -994, 1748, 116, -951]
  a := ![10, 6, 0, 2, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-244, -1044, 1748, 116, -951]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65, 199, 813, 1914, 1974]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![-65, 199, 813, 1914, 1974]] 
 ![![239, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![172, 0, 1, 0, 0], ![207, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![-65, 199, 813, 1914, 1974], ![-180, 568, 2293, 5394, 5562], ![-504, 1609, 6466, 15206, 15678], ![-618, 1989, 7969, 18739, 19320], ![-27, 93, 363, 851, 877]]]
  hmulB := by decide  
  f := ![![![17123, -11239, -1171, 2192, 5382]], ![![1966, -1290, -135, 252, 618]], ![![12346, -8103, -844, 1580, 3882]], ![![14841, -9746, -1012, 1899, 4662]], ![![703, -457, -51, 91, 223]]]
  g := ![![![-2349, 199, 813, 1914, 1974], ![-6622, 568, 2293, 5394, 5562], ![-18670, 1609, 6466, 15206, 15678], ![-23009, 1989, 7969, 18739, 19320], ![-1046, 93, 363, 851, 877]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1

def I239N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14, -16, 14, -9, 18]] i)))

def SI239N2: IdealEqSpanCertificate' Table ![![14, -16, 14, -9, 18]] 
 ![![239, 0, 0, 0, 0], ![85, 1, 0, 0, 0], ![184, 0, 1, 0, 0], ![144, 0, 0, 1, 0], ![138, 0, 0, 0, 1]] where
  M :=![![![14, -16, 14, -9, 18], ![-81, -53, 56, -17, -108], ![273, 248, -343, 169, 222], ![-39, -88, 260, -192, 228], ![-66, -12, -116, 118, -301]]]
  hmulB := by decide  
  f := ![![![27580, 57192, 5052, -20989, -31044]], ![![9935, 20603, 1822, -7556, -11178]], ![![21371, 44320, 3923, -16245, -24036]], ![![16629, 34488, 3058, -12628, -18690]], ![![15846, 32860, 2904, -12056, -17833]]]
  g := ![![![-10, -16, 14, -9, 18], ![48, -53, 56, -17, -108], ![-53, 248, -343, 169, 222], ![-185, -88, 260, -192, 228], ![196, -12, -116, 118, -301]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N2 : Nat.card (O ⧸ I239N2) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N2)

lemma isPrimeI239N2 : Ideal.IsPrime I239N2 := prime_ideal_of_norm_prime hp239.out _ NI239N2

def I239N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, 10, 74, 179, 186]] i)))

def SI239N3: IdealEqSpanCertificate' Table ![![-10, 10, 74, 179, 186]] 
 ![![239, 0, 0, 0, 0], ![159, 1, 0, 0, 0], ![53, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![94, 0, 0, 0, 1]] where
  M :=![![![-10, 10, 74, 179, 186], ![-21, 43, 210, 499, 516], ![-51, 138, 593, 1401, 1446], ![-57, 182, 732, 1722, 1776], ![0, 14, 34, 76, 77]]]
  hmulB := by decide  
  f := ![![![-5516, 3562, 416, -721, -1728]], ![![-3657, 2361, 276, -478, -1146]], ![![-1229, 796, 91, -160, -384]], ![![-213, 136, 18, -29, -66]], ![![-2164, 1398, 162, -282, -679]]]
  g := ![![![-103, 10, 74, 179, 186], ![-297, 43, 210, 499, 516], ![-845, 138, 593, 1401, 1446], ![-1047, 182, 732, 1722, 1776], ![-50, 14, 34, 76, 77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N3 : Nat.card (O ⧸ I239N3) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N3)

lemma isPrimeI239N3 : Ideal.IsPrime I239N3 := prime_ideal_of_norm_prime hp239.out _ NI239N3
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![-61, 126, -62, 20, 6]] ![![-65, 199, 813, 1914, 1974]]
  ![![11, 9, -9, 4, 24]] where
 M := ![![![11, 9, -9, 4, 24]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI239N1 : IdealMulLeCertificate' Table 
  ![![11, 9, -9, 4, 24]] ![![14, -16, 14, -9, 18]]
  ![![-4772, -3525, 2001, 291, -9084]] where
 M := ![![![-4772, -3525, 2001, 291, -9084]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI239N2 : IdealMulLeCertificate' Table 
  ![![-4772, -3525, 2001, 291, -9084]] ![![-10, 10, 74, 179, 186]]
  ![![239, 0, 0, 0, 0]] where
 M := ![![![3107, 2629, -2629, 956, 4302]]]
 hmul := by decide  
 g := ![![![![13, 11, -11, 4, 18]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1, I239N2, I239N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
    exact isPrimeI239N2
    exact isPrimeI239N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0 ⊙ MulI239N1 ⊙ MulI239N2)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0, 0, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0, 0, 0]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![0, 0, 0, 241, 0], ![0, 0, 0, 0, 241]] where
  M :=![![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![0, 0, 0, 241, 0], ![0, 0, 0, 0, 241]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 5 2 7 [191, 212, 82, 78, 75, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [216, 160, 96, 84, 157], [89, 146, 128, 0, 191], [137, 29, 220, 147, 194], [206, 146, 38, 10, 181], [0, 1]]
 g := ![![[120, 62, 60, 141, 151], [212, 51, 88, 16], [25, 124, 52, 233], [45, 8, 61, 154], [135, 219, 46, 198, 82], [4, 166, 1], []], ![[67, 234, 192, 123, 117, 21, 44, 129], [157, 131, 145, 235], [80, 82, 239, 53], [168, 93, 179, 32], [91, 238, 134, 213, 3, 226, 238, 142], [23, 217, 47, 47, 160, 89, 208, 208], [19, 99, 176, 89, 175, 58, 123, 156]], ![[79, 151, 67, 236, 78, 54, 135, 209], [181, 110, 188, 82], [177, 25, 153, 72], [145, 37, 128, 226], [151, 202, 23, 12, 5, 139, 56, 233], [20, 139, 144, 42, 207, 36, 46, 240], [35, 59, 20, 63, 192, 172, 100, 79]], ![[146, 123, 153, 4, 111, 187, 25, 205], [45, 69, 94, 100], [83, 161, 187, 94], [7, 46, 38, 125], [18, 172, 61, 167, 33, 0, 123, 120], [198, 219, 128, 31, 2, 59, 128, 54], [94, 227, 186, 132, 7, 25, 62, 48]], ![[46, 206, 191, 43, 45, 98, 235, 32], [178, 25, 85, 61], [20, 159, 134, 162], [222, 6, 53, 159], [34, 106, 33, 124, 141, 174, 68, 223], [232, 181, 108, 157, 192, 178, 65, 96], [56, 193, 85, 126, 125, 47, 12, 177]]]
 h' := ![![[216, 160, 96, 84, 157], [150, 83, 5, 195, 174], [40, 58, 144, 80, 237], [85, 168, 145, 48, 165], [2, 158, 103, 129, 201], [200, 222, 198, 83, 166], [0, 0, 0, 1], [0, 1]], ![[89, 146, 128, 0, 191], [228, 70, 64, 126, 198], [191, 79, 111, 58, 41], [23, 56, 64, 29, 189], [96, 144, 103, 99, 153], [156, 212, 79, 11, 168], [26, 154, 11, 5, 238], [216, 160, 96, 84, 157]], ![[137, 29, 220, 147, 194], [229, 88, 211, 194, 49], [133, 17, 193, 67, 166], [21, 55, 73, 31, 109], [1, 133, 28, 175, 181], [49, 52, 217, 110, 145], [107, 71, 1, 185, 46], [89, 146, 128, 0, 191]], ![[206, 146, 38, 10, 181], [90, 52, 138, 157, 126], [3, 140, 231, 211, 10], [51, 232, 4, 35, 217], [122, 207, 95, 29, 208], [42, 234, 25, 142, 231], [4, 226, 178, 17, 173], [137, 29, 220, 147, 194]], ![[0, 1], [13, 189, 64, 51, 176], [111, 188, 44, 66, 28], [202, 212, 196, 98, 43], [46, 81, 153, 50, 221], [169, 3, 204, 136, 13], [172, 31, 51, 33, 25], [206, 146, 38, 10, 181]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78, 0, 191, 42], [], [], []]
 b := ![[], [191, 141, 193, 112, 121], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 5
  hpos := by decide
  P := [191, 212, 82, 78, 75, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-470338251, -456121902, 738897806, -308534466, -171361122]
  a := ![6, 6, -3, 5, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1951611, -1892622, 3065966, -1280226, -711042]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 812990017201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def PBC241 : ContainsPrimesAboveP 241 ![I241N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![241, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 241 (by decide) 𝕀

instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0, 0, 0]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0, 0, 0]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![0, 0, 0, 251, 0], ![0, 0, 0, 0, 251]] where
  M :=![![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![0, 0, 0, 251, 0], ![0, 0, 0, 0, 251]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 5 2 7 [250, 49, 157, 215, 71, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [244, 178, 28, 23, 218], [69, 4, 50, 174, 160], [5, 142, 153, 125, 11], [113, 177, 20, 180, 113], [0, 1]]
 g := ![![[244, 12, 74, 166, 17], [24, 244, 4, 202, 92], [51, 224, 66, 155], [99, 113, 41, 7, 75], [159, 70, 139, 132, 38], [57, 180, 1], []], ![[107, 147, 163, 204, 236, 204, 104, 28], [169, 233, 42, 167, 149, 218, 73, 119], [245, 126, 39, 35], [121, 151, 197, 0, 155, 160, 207, 86], [50, 250, 189, 135, 138, 157, 215, 161], [65, 247, 125, 202, 224, 51, 167, 154], [113, 21, 232, 73, 159, 196, 204, 207]], ![[39, 184, 131, 136, 220, 209, 159, 132], [247, 144, 243, 24, 127, 79, 188, 200], [149, 36, 72, 3], [117, 161, 15, 129, 13, 230, 3, 59], [7, 235, 224, 208, 2, 17, 64, 129], [213, 54, 82, 224, 61, 34, 59, 102], [235, 87, 27, 194, 215, 195, 90, 182]], ![[93, 51, 93, 149, 159, 151, 166, 47], [145, 0, 161, 171, 44, 37, 86, 44], [109, 202, 32, 190], [81, 107, 186, 109, 142, 228, 88, 146], [224, 175, 132, 80, 247, 212, 222, 96], [10, 67, 49, 121, 226, 5, 67, 90], [38, 98, 230, 75, 184, 164, 70, 76]], ![[77, 150, 249, 54, 148, 218, 211, 28], [171, 97, 77, 229, 147, 87, 72, 161], [56, 31, 92, 207], [220, 102, 44, 137, 58, 44, 140, 39], [120, 55, 133, 71, 134, 234, 70, 195], [66, 126, 21, 201, 247, 104, 111, 23], [143, 214, 3, 211, 246, 130, 2, 149]]]
 h' := ![![[244, 178, 28, 23, 218], [24, 25, 240, 230, 45], [63, 43, 103, 126, 208], [99, 212, 115, 188, 197], [159, 46, 164, 188, 129], [57, 148, 53, 98, 17], [0, 0, 0, 1], [0, 1]], ![[69, 4, 50, 174, 160], [102, 110, 204, 167, 78], [116, 0, 143, 16, 2], [154, 204, 231, 34, 170], [103, 64, 190, 238, 16], [241, 97, 149, 12, 40], [21, 68, 173, 175, 189], [244, 178, 28, 23, 218]], ![[5, 142, 153, 125, 11], [119, 37, 145, 114, 22], [241, 100, 84, 55, 8], [208, 250, 186, 155, 175], [171, 201, 41, 155, 244], [79, 186, 190, 210, 67], [185, 22, 137, 72, 25], [69, 4, 50, 174, 160]], ![[113, 177, 20, 180, 113], [2, 143, 106, 234, 179], [154, 58, 50, 73, 2], [48, 245, 106, 59, 21], [239, 155, 133, 44, 136], [76, 70, 86, 160, 10], [163, 101, 189, 39, 223], [5, 142, 153, 125, 11]], ![[0, 1], [172, 187, 58, 8, 178], [32, 50, 122, 232, 31], [27, 93, 115, 66, 190], [77, 36, 225, 128, 228], [12, 1, 24, 22, 117], [41, 60, 3, 215, 65], [113, 177, 20, 180, 113]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [155, 77, 11, 124], [], [], []]
 b := ![[], [157, 239, 179, 246, 57], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 5
  hpos := by decide
  P := [250, 49, 157, 215, 71, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![71739565, 90105988, -24913758, 215657945, 240322460]
  a := ![3, 4, 0, 5, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![285815, 358988, -99258, 859195, 957460]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 996250626251 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def PBC251 : ContainsPrimesAboveP 251 ![I251N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![251, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 251 (by decide) 𝕀



lemma PB402I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)

def PB402I5 : PrimesBelowBoundCertificateInterval O 197 251 402 where
  m := 9
  g := ![1, 2, 2, 2, 2, 3, 4, 1, 1]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB402I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1]
    · exact ![I233N0, I233N1, I233N2]
    · exact ![I239N0, I239N1, I239N2, I239N3]
    · exact ![I241N0]
    · exact ![I251N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
    · exact PBC239
    · exact PBC241
    · exact PBC251
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![312079600999]
    · exact ![9393931, 44521]
    · exact ![2472973441, 223]
    · exact ![2655237841, 227]
    · exact ![12008989, 52441]
    · exact ![12649337, 233, 233]
    · exact ![57121, 239, 239, 239]
    · exact ![812990017201]
    · exact ![996250626251]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
      exact NI233N2
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
      exact NI239N2
      exact NI239N3
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
  β := ![I223N1, I227N1, I233N1, I233N2, I239N1, I239N2, I239N3]
  Il := ![[], [], [I223N1], [I227N1], [], [I233N1, I233N2], [I239N1, I239N2, I239N3], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
