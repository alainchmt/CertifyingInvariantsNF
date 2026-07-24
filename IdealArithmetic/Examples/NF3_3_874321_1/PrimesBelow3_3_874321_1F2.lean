
import IdealArithmetic.Examples.NF3_3_874321_1.RI3_3_874321_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11064, -280, 229]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-11064, -280, 229]] 
 ![![83, 0, 0], ![0, 83, 0], ![22, 14, 1]] where
  M :=![![![-11064, -280, 229], ![40533, 1022, -840], ![-63071, -1609, 1302]]]
  hmulB := by decide  
  f := ![![![-252, -47, 14]], ![![2478, 457, -141]], ![![241, 44, -14]]]
  g := ![![![-194, -42, 229], ![711, 154, -840], ![-1105, -239, 1302]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [63, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 82], [0, 1]]
 g := ![![[21, 29], [67, 64], [31], [63], [76, 25], [1]], ![[0, 54], [55, 19], [31], [63], [35, 58], [1]]]
 h' := ![![[5, 82], [12, 64], [21, 75], [27, 60], [26, 35], [20, 5], [0, 1]], ![[0, 1], [0, 19], [64, 8], [78, 23], [35, 48], [45, 78], [5, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [4, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [63, 78, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2128, 2403, 972]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-232, -135, 972]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-252, -47, 14]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-252, -47, 14]] 
 ![![83, 0, 0], ![41, 1, 0], ![7, 0, 1]] where
  M :=![![![-252, -47, 14], ![2478, 457, -141], ![-9145, -1712, 504]]]
  hmulB := by decide  
  f := ![![![-11064, -280, 229]], ![![-4977, -126, 103]], ![![-1693, -43, 35]]]
  g := ![![![19, -47, 14], ![-184, 457, -141], ![693, -1712, 504]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-11064, -280, 229]] ![![-252, -47, 14]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![440, 65, -21]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![440, 65, -21]] 
 ![![89, 0, 0], ![0, 89, 0], ![85, 52, 1]] where
  M :=![![![440, 65, -21], ![-3717, -629, 195], ![12744, 2271, -694]]]
  hmulB := by decide  
  f := ![![![-71, -29, -6]], ![![-1062, -424, -87]], ![![-742, -297, -61]]]
  g := ![![![25, 13, -21], ![-228, -121, 195], ![806, 431, -694]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [63, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 88], [0, 1]]
 g := ![![[77, 39], [47], [10], [8, 39], [74, 67], [1]], ![[13, 50], [47], [10], [33, 50], [85, 22], [1]]]
 h' := ![![[44, 88], [74, 22], [3, 15], [30, 30], [55, 67], [26, 44], [0, 1]], ![[0, 1], [63, 67], [40, 74], [15, 59], [66, 22], [4, 45], [44, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [70, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [63, 45, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![314, 2059, 1568]
  a := ![-1, 1, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1494, -893, 1568]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 29, 6]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![71, 29, 6]] 
 ![![89, 0, 0], ![22, 1, 0], ![39, 0, 1]] where
  M :=![![![71, 29, 6], ![1062, 424, 87], ![4779, 1920, 395]]]
  hmulB := by decide  
  f := ![![![-440, -65, 21]], ![![-67, -9, 3]], ![![-336, -54, 17]]]
  g := ![![![-9, 29, 6], ![-131, 424, 87], ![-594, 1920, 395]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![440, 65, -21]] ![![71, 29, 6]]
  ![![89, 0, 0]] where
 M := ![![![-89, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7440, 2971, 605]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![7440, 2971, 605]] 
 ![![97, 0, 0], ![0, 97, 0], ![62, 87, 1]] where
  M :=![![![7440, 2971, 605], ![107085, 43081, 8913], ![490172, 196129, 40110]]]
  hmulB := by decide  
  f := ![![![207411, 5245, -4294]], ![![-760038, -19220, 15735]], ![![-536929, -13578, 11116]]]
  g := ![![![-310, -512, 605], ![-4593, -7550, 8913], ![-20584, -33953, 40110]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [18, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 96], [0, 1]]
 g := ![![[39, 27], [3], [2], [89], [94], [74, 1]], ![[0, 70], [3], [2], [89], [94], [51, 96]]]
 h' := ![![[74, 96], [11, 30], [29, 87], [29, 14], [51, 63], [26, 26], [0, 1]], ![[0, 1], [0, 67], [65, 10], [95, 83], [57, 34], [10, 71], [74, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [32, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [18, 23, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2583, 59, 159]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-75, -142, 159]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-207411, -5245, 4294]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-207411, -5245, 4294]] 
 ![![97, 0, 0], ![30, 1, 0], ![78, 0, 1]] where
  M :=![![![-207411, -5245, 4294], ![760038, 19220, -15735], ![-1181711, -29884, 24465]]]
  hmulB := by decide  
  f := ![![![-7440, -2971, -605]], ![![-3405, -1363, -279]], ![![-11036, -4411, -900]]]
  g := ![![![-3969, -5245, 4294], ![14544, 19220, -15735], ![-22613, -29884, 24465]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![7440, 2971, 605]] ![![-207411, -5245, 4294]]
  ![![97, 0, 0]] where
 M := ![![![-97, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [41, 81, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [87, 80, 96], [67, 20, 5], [0, 1]]
 g := ![![[57, 1, 54], [95, 23], [39, 73, 100], [32, 80], [2, 82], [1]], ![[80, 59, 63, 13], [18, 54], [72, 40, 10, 70], [], [31, 76], [43, 39, 82, 77]], ![[78, 75, 93, 65], [25, 52], [11, 26, 14, 9], [64, 80], [47, 9], [21, 53, 45, 24]]]
 h' := ![![[87, 80, 96], [30, 40, 16], [17, 77, 15], [88, 24, 91], [84, 88, 22], [60, 20, 53], [0, 1]], ![[67, 20, 5], [91, 83, 19], [83, 50, 16], [33, 68, 84], [72, 65], [38, 43, 51], [87, 80, 96]], ![[0, 1], [1, 79, 66], [4, 75, 70], [94, 9, 27], [71, 49, 79], [33, 38, 98], [67, 20, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 3], []]
 b := ![[], [3, 58, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [41, 81, 48, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5197965, -2839211, -911323]
  a := ![1, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-51465, -28111, -9023]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8726, -1607, 498]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-8726, -1607, 498]] 
 ![![103, 0, 0], ![0, 103, 0], ![71, 40, 1]] where
  M :=![![![-8726, -1607, 498], ![88146, 16559, -4821], ![-313821, -57396, 18166]]]
  hmulB := by decide  
  f := ![![![-234026, -5918, 4845]], ![![857565, 21686, -17754]], ![![158771, 4015, -3287]]]
  g := ![![![-428, -209, 498], ![4179, 2033, -4821], ![-15569, -7612, 18166]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [6, 89, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 102], [0, 1]]
 g := ![![[32, 98], [1, 81], [0, 98], [18], [50], [14, 1]], ![[65, 5], [2, 22], [33, 5], [18], [50], [28, 102]]]
 h' := ![![[14, 102], [97, 43], [0, 94], [8, 43], [61, 92], [19, 87], [0, 1]], ![[0, 1], [81, 60], [80, 9], [95, 60], [10, 11], [1, 16], [14, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [42, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [6, 89, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2071, 2381, 917]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-612, -333, 917]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![234026, 5918, -4845]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![234026, 5918, -4845]] 
 ![![103, 0, 0], ![86, 1, 0], ![81, 0, 1]] where
  M :=![![![234026, 5918, -4845], ![-857565, -21686, 17754], ![1333341, 33717, -27604]]]
  hmulB := by decide  
  f := ![![![8726, 1607, -498]], ![![6430, 1181, -369]], ![![9909, 1821, -568]]]
  g := ![![![1141, 5918, -4845], ![-4181, -21686, 17754], ![6501, 33717, -27604]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-8726, -1607, 498]] ![![234026, 5918, -4845]]
  ![![103, 0, 0]] where
 M := ![![![-103, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![226014, 41965, -12679]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![226014, 41965, -12679]] 
 ![![107, 0, 0], ![0, 107, 0], ![60, 42, 1]] where
  M :=![![![226014, 41965, -12679], ![-2244183, -416687, 125895], ![8175866, 1518049, -458652]]]
  hmulB := by decide  
  f := ![![![4233, 113, -86]], ![![-15222, -298, 339]], ![![-3367, -44, 81]]]
  g := ![![![9222, 5369, -12679], ![-91569, -53311, 125895], ![333598, 194219, -458652]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [96, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 106], [0, 1]]
 g := ![![[91, 89], [105, 1], [33], [55, 19], [30], [38, 1]], ![[49, 18], [36, 106], [33], [28, 88], [30], [76, 106]]]
 h' := ![![[38, 106], [85, 14], [20, 106], [70, 56], [2, 74], [97, 64], [0, 1]], ![[0, 1], [82, 93], [89, 1], [58, 51], [32, 33], [68, 43], [38, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [39, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [96, 69, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![191267, 189559, 94885]
  a := ![1, 20, 41]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-51419, -35473, 94885]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4233, 113, -86]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![4233, 113, -86]] 
 ![![107, 0, 0], ![88, 1, 0], ![100, 0, 1]] where
  M :=![![![4233, 113, -86], ![-15222, -298, 339], ![25075, 1028, -411]]]
  hmulB := by decide  
  f := ![![![226014, 41965, -12679]], ![![164907, 30619, -9251]], ![![287638, 53407, -16136]]]
  g := ![![![27, 113, -86], ![-214, -298, 339], ![-227, 1028, -411]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![226014, 41965, -12679]] ![![4233, 113, -86]]
  ![![107, 0, 0]] where
 M := ![![![107, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, 8, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![21, 8, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![21, 8, 1]] where
  M :=![![![21, 8, 1], ![177, 83, 24], ![1357, 491, 75]]]
  hmulB := by decide  
  f := ![![![-51, -1, 1]], ![![177, 2, -3]], ![![1, 0, 0]]]
  g := ![![![0, 0, 1], ![-3, -1, 24], ![-2, -1, 75]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [24, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 108], [0, 1]]
 g := ![![[66, 48], [20], [75, 21], [64, 3], [104], [51, 1]], ![[7, 61], [20], [56, 88], [108, 106], [104], [102, 108]]]
 h' := ![![[51, 108], [40, 22], [53, 42], [99, 28], [91, 60], [84, 70], [0, 1]], ![[0, 1], [72, 87], [15, 67], [1, 81], [99, 49], [57, 39], [51, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [29, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [24, 58, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1560, 1295, 666]
  a := ![-1, 2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-114, -37, 666]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51, -1, 1]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-51, -1, 1]] 
 ![![109, 0, 0], ![85, 1, 0], ![34, 0, 1]] where
  M :=![![![-51, -1, 1], ![177, 2, -3], ![-236, 5, 3]]]
  hmulB := by decide  
  f := ![![![21, 8, 1]], ![![18, 7, 1]], ![![19, 7, 1]]]
  g := ![![![0, -1, 1], ![1, 2, -3], ![-7, 5, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![21, 8, 1]] ![![-51, -1, 1]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-259, -52, 12]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-259, -52, 12]] 
 ![![113, 0, 0], ![0, 113, 0], ![82, 71, 1]] where
  M :=![![![-259, -52, 12], ![2124, 337, -156], ![-9912, -2100, 389]]]
  hmulB := by decide  
  f := ![![![-1739, -44, 36]], ![![6372, 161, -132]], ![![2654, 67, -55]]]
  g := ![![![-11, -8, 12], ![132, 101, -156], ![-370, -263, 389]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [92, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 112], [0, 1]]
 g := ![![[105, 8], [88], [111], [50], [5, 25], [58, 1]], ![[4, 105], [88], [111], [50], [99, 88], [3, 112]]]
 h' := ![![[58, 112], [71, 11], [101, 38], [97, 87], [105, 84], [88, 108], [0, 1]], ![[0, 1], [31, 102], [45, 75], [58, 26], [5, 29], [24, 5], [58, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [1, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [92, 55, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![28290, 23252, 9950]
  a := ![2, -8, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6970, -6046, 9950]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1739, -44, 36]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-1739, -44, 36]] 
 ![![113, 0, 0], ![13, 1, 0], ![90, 0, 1]] where
  M :=![![![-1739, -44, 36], ![6372, 161, -132], ![-9912, -252, 205]]]
  hmulB := by decide  
  f := ![![![-259, -52, 12]], ![![-11, -3, 0]], ![![-294, -60, 13]]]
  g := ![![![-39, -44, 36], ![143, 161, -132], ![-222, -252, 205]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-259, -52, 12]] ![![-1739, -44, 36]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-408, -1, 11]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-408, -1, 11]] 
 ![![127, 0, 0], ![0, 127, 0], ![113, 23, 1]] where
  M :=![![![-408, -1, 11], ![1947, 185, -3], ![-826, 595, 186]]]
  hmulB := by decide  
  f := ![![![285, 53, -16]], ![![-2832, -526, 159]], ![![-178, -33, 10]]]
  g := ![![![-13, -2, 11], ![18, 2, -3], ![-172, -29, 186]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [38, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 126], [0, 1]]
 g := ![![[51, 117], [122, 68], [68, 88], [93, 84], [111, 82], [94, 1]], ![[0, 10], [37, 59], [85, 39], [115, 43], [72, 45], [61, 126]]]
 h' := ![![[94, 126], [63, 25], [83, 103], [22, 56], [100, 81], [111, 35], [0, 1]], ![[0, 1], [0, 102], [113, 24], [79, 71], [94, 46], [99, 92], [94, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74]]
 b := ![[], [39, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [38, 33, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![577, 59, 113]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-96, -20, 113]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![285, 53, -16]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![285, 53, -16]] 
 ![![127, 0, 0], ![58, 1, 0], ![87, 0, 1]] where
  M :=![![![285, 53, -16], ![-2832, -526, 159], ![10325, 1918, -579]]]
  hmulB := by decide  
  f := ![![![-408, -1, 11]], ![![-171, 1, 5]], ![![-286, 4, 9]]]
  g := ![![![-11, 53, -16], ![109, -526, 159], ![-398, 1918, -579]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-408, -1, 11]] ![![285, 53, -16]]
  ![![127, 0, 0]] where
 M := ![![![127, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [40, 69, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 103, 53], [57, 27, 78], [0, 1]]
 g := ![![[41, 84, 99], [72, 84, 99], [68, 4], [3, 9], [99, 84], [120, 1], []], ![[49, 76, 37, 107], [89, 41, 37, 107], [50, 108], [99, 33], [124, 112], [93, 74], [62, 58]], ![[99, 106, 50, 118], [100, 11, 50, 118], [61, 107], [97, 39], [75, 1], [65, 129], [37, 58]]]
 h' := ![![[63, 103, 53], [2, 76, 112], [46, 76, 112], [88, 28, 2], [83, 17, 3], [47, 64, 52], [0, 0, 1], [0, 1]], ![[57, 27, 78], [79, 54, 109], [123, 54, 109], [114, 55, 97], [119, 62, 65], [25, 110, 80], [48, 92, 27], [63, 103, 53]], ![[0, 1], [67, 1, 41], [111, 1, 41], [113, 48, 32], [71, 52, 63], [53, 88, 130], [66, 39, 103], [57, 27, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 121], []]
 b := ![[], [95, 1, 104], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [40, 69, 11, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26900457, -13801636, -4166455]
  a := ![1, -5, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-205347, -105356, -31805]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1914, 272, -161]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![1914, 272, -161]] 
 ![![137, 0, 0], ![0, 137, 0], ![23, 80, 1]] where
  M :=![![![1914, 272, -161], ![-28497, -6508, 816], ![57643, 5189, -6780]]]
  hmulB := by decide  
  f := ![![![291168, 7363, -6028]], ![![-1066956, -26981, 22089]], ![![-562049, -14213, 11636]]]
  g := ![![![41, 96, -161], ![-345, -524, 816], ![1559, 3997, -6780]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [5, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [100, 136], [0, 1]]
 g := ![![[117, 107], [18], [30], [39, 100], [16], [136], [1]], ![[131, 30], [18], [30], [38, 37], [16], [136], [1]]]
 h' := ![![[100, 136], [43, 92], [63, 93], [79, 116], [135, 127], [30, 133], [132, 100], [0, 1]], ![[0, 1], [64, 45], [47, 44], [34, 21], [94, 10], [41, 4], [131, 37], [100, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85]]
 b := ![[], [67, 111]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [5, 37, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-156, 59, 23]
  a := ![-3, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5, -13, 23]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![291168, 7363, -6028]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![291168, 7363, -6028]] 
 ![![137, 0, 0], ![34, 1, 0], ![60, 0, 1]] where
  M :=![![![291168, 7363, -6028], ![-1066956, -26981, 22089], ![1658903, 41950, -34344]]]
  hmulB := by decide  
  f := ![![![1914, 272, -161]], ![![267, 20, -34]], ![![1259, 157, -120]]]
  g := ![![![2938, 7363, -6028], ![-10766, -26981, 22089], ![16739, 41950, -34344]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![1914, 272, -161]] ![![291168, 7363, -6028]]
  ![![137, 0, 0]] where
 M := ![![![137, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)


lemma PB208I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB208I2 : PrimesBelowBoundCertificateInterval O 79 137 208 where
  m := 11
  g := ![2, 2, 2, 1, 2, 2, 2, 2, 2, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB208I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0]
    · exact ![I137N0, I137N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
    · exact ![2248091]
    · exact ![18769, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I97N1, I103N1, I107N1, I109N1, I113N1, I127N1, I137N1]
  Il := ![[I83N1], [I89N1], [I97N1], [], [I103N1], [I107N1], [I109N1], [I113N1], [I127N1], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
