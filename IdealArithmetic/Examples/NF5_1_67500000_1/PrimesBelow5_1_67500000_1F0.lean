
import IdealArithmetic.Examples.NF5_1_67500000_1.RI5_1_67500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![1, 1, 0, 1, 2], ![6, 15, 12, 9, -1]]]
  hmulB := by decide  
  f := ![![![0, -16, -10, -4, 11], ![12, -4, 0, -10, 2]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, 0, 0, 0, -1], ![-1, 0, 0, 1, 0]], ![![0, -8, -5, -2, 6], ![6, -2, 0, -5, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-1, 1, 0, 2, 0], ![-1, 1, 0, 1, 2], ![-1, 15, 12, 9, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, 20, 14, 16, 5]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![8, 20, 14, 16, 5]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![8, 20, 14, 16, 5], ![46, 113, 80, 89, 27], ![251, 620, 437, 492, 151], ![676, 1666, 1176, 1318, 403], ![1503, 3708, 2616, 2937, 899]]]
  hmulB := by decide  
  f := ![![![-41, -26, -2, 3, 0]], ![![-19, -33, -14, 1, 3]], ![![-3, 20, 15, 2, -4]], ![![-33, -16, -2, 0, 1]], ![![18, 18, 12, 3, -4]]]
  g := ![![![-21, 20, 14, 16, 5], ![-118, 113, 80, 89, 27], ![-649, 620, 437, 492, 151], ![-1742, 1666, 1176, 1318, 403], ![-3879, 3708, 2616, 2937, 899]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-6, -9, -4, 0, 1]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![-6, -9, -4, 0, 1]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![-6, -9, -4, 0, 1], ![6, 5, 3, 1, -1], ![-5, -5, -7, -2, 3], ![5, 13, 14, 5, -3], ![-9, -15, -18, 0, 8]]]
  hmulB := by decide  
  f := ![![![174, -116, 76, 108, -57], ![-138, -176, 20, 0, 2]], ![![90, -53, 40, 54, -29], ![-68, -88, 10, 0, 1]], ![![168, -111, 74, 104, -55], ![-133, -170, 19, 0, 2]], ![![12, 2, 6, 5, -3], ![-4, -7, 1, 0, 0]], ![![87, -58, 38, 54, -28], ![-69, -88, 10, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![3, -9, -4, 0, 1], ![-1, 5, 3, 1, -1], ![3, -5, -7, -2, 3], ![-12, 13, 14, 5, -3], ![8, -15, -18, 0, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![8, 20, 14, 16, 5]]
  ![![2, 0, 0, 0, 0], ![-1, 6, 5, 0, -1]] where
 M := ![![![16, 40, 28, 32, 10]], ![![46, 113, 80, 89, 27]]]
 hmul := by decide  
 g := ![![![![1005, 378, -93, -94, 28], ![386, 256, 0, 0, 12]]], ![![![2847, 1068, -265, -267, 79], ![1094, 725, 0, 0, 34]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![-1, 6, 5, 0, -1]] ![![8, 20, 14, 16, 5]]
  ![![2, 0, 0, 0, 0], ![0, -2, -3, -1, 1]] where
 M := ![![![16, 40, 28, 32, 10]], ![![20, 50, 35, 41, 13]]]
 hmul := by decide  
 g := ![![![![48, 52, 10, 4, 9], ![-56, -16, 0, 0, 0]]], ![![![60, 64, 11, 5, 12], ![-71, -20, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![0, -2, -3, -1, 1]] ![![2, 0, 0, 0, 0], ![-6, -9, -4, 0, 1]]
  ![![2, 0, 0, 0, 0], ![-7, -11, -7, -1, 2]] where
 M := ![![![4, 0, 0, 0, 0], ![-12, -18, -8, 0, 2]], ![![0, -4, -6, -2, 2], ![-11, -23, -17, -1, 4]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![1, 2, 3, 1, -1], ![2, 0, 0, 0, 0]]], ![![![0, -2, -3, -1, 1], ![0, 0, 0, 0, 0]], ![![5, 5, 2, 1, -1], ![3, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![-7, -11, -7, -1, 2]] ![![2, 0, 0, 0, 0], ![-6, -9, -4, 0, 1]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![-12, -18, -8, 0, 2]], ![![-14, -22, -14, -2, 4], ![-12, 0, -6, -2, 2]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0]], ![![-6, -9, -4, 0, 1]]], ![![![-7, -11, -7, -1, 2]], ![![-6, 0, -3, -1, 1]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N2, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 2, 2, 5, 2]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![2, 2, 2, 5, 2]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 1, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 2, 2, 5, 2], ![17, 39, 26, 27, 8], ![75, 190, 135, 151, 46], ![205, 506, 358, 404, 124], ![462, 1140, 804, 900, 275]]]
  hmulB := by decide  
  f := ![![![-28, -54, -50, -13, 16]], ![![83, 149, 138, 31, -42]], ![![-83, -144, -135, -28, 40]], ![![106, 177, 168, 31, -48]], ![![-140, -224, -216, -34, 59]]]
  g := ![![![0, -1, 2, 5, 2], ![-3, 4, 26, 27, 8], ![-20, 13, 135, 151, 46], ![-51, 34, 358, 404, 124], ![-114, 80, 804, 900, 275]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2], [0, 1]]
 g := ![![[2, 1]], ![[1, 2]]]
 h' := ![![[2, 2], [0, 1]], ![[0, 1], [2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [2, 1, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18632, 47183, 32609, 39134, 13002]
  a := ![-5, -7, -3, -8, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4659, 2683, 32609, 39134, 13002]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 2, 0], ![1, 1, 0, 2, 2], ![6, 15, 12, 9, 0]]]
  hmulB := by decide  
  f := ![![![0, -1, 0, 0, 0], ![3, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, -1, 0, 0, 0], ![2, 1, 0, 0, 0]], ![![0, -1, -1, -1, 0], ![0, 1, 2, 0, 0]], ![![-2, 0, 2, 4, -1], ![4, 2, -8, 2, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-1, 1, 1, 2, 0], ![0, 1, 0, 2, 2], ![-11, 15, 12, 9, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![2, 2, 2, 5, 2]] ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0], ![-7, -8, -1, 1, 0]] where
 M := ![![![6, 6, 6, 15, 6], ![19, 41, 28, 32, 10]]]
 hmul := by decide  
 g := ![![![![-16, 14, 32, 11, -6], ![-6, 12, 0, 0, 0]], ![![-26, 31, 59, 21, -10], ![-11, 20, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![-7, -8, -1, 1, 0]] ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0], ![6, 15, 9, 0, -2]] where
 M := ![![![9, 0, 0, 0, 0], ![3, 3, 0, 0, 0]], ![![-21, -24, -3, 3, 0], ![-6, -15, -9, 0, 2]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![1, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![-7, -8, -1, 1, 0], ![0, 0, 0, 0, 0]], ![![-6, -15, -9, 0, 2], ![2, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![6, 15, 9, 0, -2]] ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![9, 0, 0, 0, 0], ![3, 3, 0, 0, 0]], ![![18, 45, 27, 0, -6], ![-6, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0]], ![![1, 1, 0, 0, 0]]], ![![![6, 15, 9, 0, -2]], ![![-2, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![639, 1576, 1112, 1248, 382]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![639, 1576, 1112, 1248, 382]] 
 ![![5, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![639, 1576, 1112, 1248, 382], ![3540, 8729, 6160, 6910, 2114], ![19594, 48320, 34097, 38256, 11706], ![52476, 129404, 91316, 102447, 31346], ![116934, 288360, 203484, 228294, 69853]]]
  hmulB := by decide  
  f := ![![![63, -696, -448, 4, 94]], ![![164, -351, -272, -6, 58]], ![![-62, -624, -359, 12, 74]], ![![-56, -164, -84, 3, 18]], ![![33, -24, -20, 2, 3]]]
  g := ![![![-2099, 1576, 1112, 1248, 382], ![-11626, 8729, 6160, 6910, 2114], ![-64356, 48320, 34097, 38256, 11706], ![-172350, 129404, 91316, 102447, 31346], ![-384059, 288360, 203484, 228294, 69853]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![639, 1576, 1112, 1248, 382]] ![![639, 1576, 1112, 1248, 382]]
  ![![137934725, 340145520, 240027848, 269290468, 82396488]] where
 M := ![![![137934725, 340145520, 240027848, 269290468, 82396488]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![137934725, 340145520, 240027848, 269290468, 82396488]] ![![639, 1576, 1112, 1248, 382]]
  ![![29761598610347, 73391775986792, 51789804690736, 58103677839756, 17778345569110]] where
 M := ![![![29761598610347, 73391775986792, 51789804690736, 58103677839756, 17778345569110]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![29761598610347, 73391775986792, 51789804690736, 58103677839756, 17778345569110]] ![![639, 1576, 1112, 1248, 382]]
  ![![6421535640712881193, 15835436510139322784, 11174469523673308112, 12536787522387123464, 3835959257419018864]] where
 M := ![![![6421535640712881193, 15835436510139322784, 11174469523673308112, 12536787522387123464, 3835959257419018864]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![6421535640712881193, 15835436510139322784, 11174469523673308112, 12536787522387123464, 3835959257419018864]] ![![639, 1576, 1112, 1248, 382]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![1385547884198985775624055, 3416745896866995501672040, 2411068546814573939691720, 2705010202881529601353400, 827668883326544090549710]]]
 hmul := by decide  
 g := ![![![![277109576839797155124811, 683349179373399100334408, 482213709362914787938344, 541002040576305920270680, 165533776665308818109942]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1 ⊙ MulI5N2 ⊙ MulI5N3)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, -5, 5, 3, -2]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-6, -5, 5, 3, -2]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![6, 3, 1, 0, 0], ![5, 6, 0, 1, 0], ![1, 5, 0, 0, 1]] where
  M :=![![![-6, -5, 5, 3, -2], ![-9, -28, -29, -5, 8], ![43, 77, 68, 9, -18], ![-45, -61, -55, -6, 14], ![69, 99, 93, 9, -23]]]
  hmulB := by decide  
  f := ![![![-6, -15, -11, -13, -4]], ![![-37, -90, -63, -71, -22]], ![![-50, -123, -87, -98, -30]], ![![-113, -278, -196, -221, -68]], ![![-200, -492, -347, -389, -119]]]
  g := ![![![-7, -4, 5, 3, -2], ![26, 7, -29, -5, 8], ![-56, -13, 68, 9, -18], ![43, 10, -55, -6, 14], ![-73, -17, 93, 9, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [6, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 6], [0, 1]]
 g := ![![[1, 4], [1, 1]], ![[5, 3], [2, 6]]]
 h' := ![![[1, 6], [1, 2], [0, 1]], ![[0, 1], [3, 5], [1, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [3, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [6, 6, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1036, 2504, 1754, 2069, 747]
  a := ![0, -4, 0, -5, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2940, -2701, 1754, 2069, 747]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![-1, -1, -3, -1, 1]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0], ![-1, -1, -3, -1, 1]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![2, 5, 1, 0, 0], ![2, 3, 0, 1, 0], ![0, 3, 0, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![-1, -1, -3, -1, 1], ![5, 10, 11, 2, -3], ![-16, -27, -26, -3, 7], ![17, 25, 23, 3, -5], ![-24, -33, -33, 0, 9]]]
  hmulB := by decide  
  f := ![![![-355, -803, -750, -107, 191], ![532, 672, 21, 0, 0]], ![![-749, -1687, -1575, -224, 401], ![1120, 1407, 42, 0, 0]], ![![-584, -1316, -1229, -175, 313], ![872, 1098, 33, 0, 0]], ![![-422, -952, -888, -126, 226], ![635, 795, 24, 0, 0]], ![![-321, -723, -675, -96, 172], ![480, 603, 18, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-2, -5, 7, 0, 0], ![-2, -3, 0, 7, 0], ![0, -3, 0, 0, 7]], ![![1, 2, -3, -1, 1], ![-3, -6, 11, 2, -3], ![6, 13, -26, -3, 7], ![-5, -12, 23, 3, -5], ![6, 15, -33, 0, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [5, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 6], [0, 1]]
 g := ![![[2, 2], [4, 1]], ![[3, 5], [1, 6]]]
 h' := ![![[4, 6], [1, 4], [0, 1]], ![[0, 1], [3, 3], [4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [6, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [5, 3, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![91866, 226501, 159955, 178823, 54414]
  a := ![9, 27, 5, 26, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-83670, -181855, 159955, 178823, 54414]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, 1, -1, 2, 0], ![1, 1, 0, 0, 2], ![6, 15, 12, 9, -2]]]
  hmulB := by decide  
  f := ![![![56, -7, 0, 0, 48], ![217, 0, 0, -168, 0]], ![![56, -7, 0, 0, 48], ![218, 0, 0, -168, 0]], ![![46, -5, 0, 0, 40], ![176, 1, 0, -140, 0]], ![![0, 0, 0, -1, 0], ![0, 4, 4, 0, 0]], ![![8, -1, 0, 0, 7], ![31, 0, 0, -24, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-6, 7, 0, 0, 0], ![-6, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![-1, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, 1, -1, 2, 0], ![-1, 1, 0, 0, 2], ![-22, 15, 12, 9, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-6, -5, 5, 3, -2]] ![![7, 0, 0, 0, 0], ![-1, -1, -3, -1, 1]]
  ![![7, 0, 0, 0, 0], ![14, 30, 19, 2, -5]] where
 M := ![![![-42, -35, 35, 21, -14], ![0, -38, -32, -10, 11]]]
 hmul := by decide  
 g := ![![![![-6, -5, 5, 3, -2], ![0, 0, 0, 0, 0]], ![![-4, -14, -10, -2, 3], ![2, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0, 0, 0], ![14, 30, 19, 2, -5]] ![![7, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![49, 0, 0, 0, 0], ![-7, 7, 0, 0, 0]], ![![98, 210, 133, 14, -35], ![-42, -70, -49, -7, 14]]]
 hmul := by decide  
 g := ![![![![7, 0, 0, 0, 0]], ![![-1, 1, 0, 0, 0]]], ![![![14, 30, 19, 2, -5]], ![![-6, -10, -7, -1, 2]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-7, -9, -5, -2, 2]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![-7, -9, -5, -2, 2]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![2, 1, 3, 10, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-7, -9, -5, -2, 2], ![10, 16, 15, 6, -6], ![-30, -59, -56, -18, 18], ![40, 75, 71, 13, -24], ![-87, -159, -147, -39, 39]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![4, 5, 3, 2, -1], ![6, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-2, -1, -3, -10, 11]], ![![-1, -1, -1, -2, 2], ![2, 2, 3, 6, -6], ![-6, -7, -10, -18, 18], ![8, 9, 13, 23, -24], ![-15, -18, -24, -39, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 4 2 3 [10, 7, 4, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 5, 0, 1], [8, 4, 4, 7], [10, 1, 7, 3], [0, 1]]
 g := ![![[10, 6, 2, 1], [6, 1], []], ![[1, 9, 7, 4, 2, 1], [10, 2, 8, 1, 0, 1], [9, 6, 1]], ![[4, 7, 3, 10, 0, 8], [1, 2, 2, 5, 4, 10], [7, 9, 5]], ![[1, 6, 9, 0, 5, 9], [5, 10, 3, 1, 0, 4], [1, 8, 9]]]
 h' := ![![[10, 5, 0, 1], [6, 3, 2, 10], [0, 0, 1], [0, 1]], ![[8, 4, 4, 7], [9, 1, 2, 10], [10, 10, 3, 10], [10, 5, 0, 1]], ![[10, 1, 7, 3], [3, 2, 2, 8], [5, 2, 5, 5], [8, 4, 4, 7]], ![[0, 1], [1, 5, 5, 5], [2, 10, 2, 7], [10, 1, 7, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [6, 8, 6], []]
 b := ![[], [], [5, 9, 0, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 4
  hpos := by decide
  P := [10, 7, 4, 5, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1359684926866, 3353389225594, 2366205918750, 2655192285998, 812506080233]
  a := ![-11, -9, -5, -7, -21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-24120657600, 230989376851, -6482938359, -497260774212, 812506080233]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 14641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![3, 1, 0, 0, 0], ![0, 3, 1, 0, 0], ![0, 1, 3, 2, 0], ![1, 1, 0, 4, 2], ![6, 15, 12, 9, 2]]]
  hmulB := by decide  
  f := ![![![-50, 46, 247, 132, -18], ![154, 55, -924, 99, 0]], ![![-54, 49, 259, 140, -18], ![166, 55, -968, 99, 0]], ![![-59, 48, 262, 142, -18], ![184, 56, -979, 99, 0]], ![![-1, -2, -2, -1, 0], ![4, 4, 6, 0, 0]], ![![-38, 34, 180, 96, -13], ![118, 36, -672, 72, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-3, 11, 0, 0, 0], ![-2, 0, 11, 0, 0], ![-1, 0, 0, 11, 0], ![-8, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![-1, 3, 1, 0, 0], ![-1, 1, 3, 2, 0], ![-2, 1, 0, 4, 2], ![-8, 15, 12, 9, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0, 0, 0], ![-7, -9, -5, -2, 2]] ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![121, 0, 0, 0, 0], ![33, 11, 0, 0, 0]], ![![-77, -99, -55, -22, 22], ![-11, -11, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![11, 0, 0, 0, 0]], ![![3, 1, 0, 0, 0]]], ![![![-7, -9, -5, -2, 2]], ![![-1, -1, 0, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![-13, -21, -19, -5, 6]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![-13, -21, -19, -5, 6]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![9, 5, 11, 1, 0], ![1, 5, 6, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![-13, -21, -19, -5, 6], ![31, 53, 51, 11, -16], ![-85, -147, -139, -31, 38], ![83, 131, 129, 11, -42], ![-171, -285, -267, -63, 58]]]
  hmulB := by decide  
  f := ![![![26, 55, 65, 5, -20], ![-130, -65, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![14, 32, 40, 2, -12], ![-94, -45, 0, 0, 0]], ![![1, 3, 4, 0, -1], ![-11, -5, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-9, -5, -11, 13, 0], ![-1, -5, -6, 0, 13]], ![![2, -2, 0, -5, 6], ![-4, 6, 2, 11, -16], ![12, -14, -2, -31, 38], ![2, 22, 20, 11, -42], ![26, -20, 6, -63, 58]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [5, 9, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 6, 5], [3, 6, 8], [0, 1]]
 g := ![![[5, 8, 12], [5, 3], [1]], ![[7, 7, 8, 6], [9, 12], [0, 1, 1, 8]], ![[2, 11, 12, 6], [6, 3], [6, 12, 2, 5]]]
 h' := ![![[1, 6, 5], [0, 4, 8], [8, 4, 4], [0, 1]], ![[3, 6, 8], [8, 2, 3], [1, 0, 5], [1, 6, 5]], ![[0, 1], [5, 7, 2], [10, 9, 4], [3, 6, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 10], []]
 b := ![[], [1, 10, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [5, 9, 9, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2087581, 188012, -2586428, 6993282, 5730724]
  a := ![6, -4, 4, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5442911, -4879386, -8761298, 6993282, 5730724]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![1, 1, 0, 1, 2], ![6, 15, 12, 9, -1]]]
  hmulB := by decide  
  f := ![![![0, 5, 0, 13, -2], ![13, 0, -91, 13, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, -1, 0, -1, 0], ![6, 0, 7, 0, 0]], ![![0, 3, 0, 7, -1], ![3, 0, -49, 7, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![-7, 0, 0, 0, 13]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![-1, 1, 0, 1, 2], ![1, 15, 12, 9, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -1, -1, 0, 0]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![-1, -1, -1, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-1, -1, -1, 0, 0], ![0, -2, -1, -2, 0], ![-2, -3, -2, -4, -4], ![-14, -33, -25, -21, -2], ![-9, -27, -15, -33, -19]]]
  hmulB := by decide  
  f := ![![![5, 131, 77, -2, -16]], ![![-6, 28, 19, 0, -4]], ![![10, 103, 58, -2, -12]], ![![6, 51, 29, -1, -6]], ![![1, 73, 43, -1, -9]]]
  g := ![![![1, -1, -1, 0, 0], ![2, -2, -1, -2, 0], ![6, -3, -2, -4, -4], ![36, -33, -25, -21, -2], ![41, -27, -15, -33, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0, 0, 0], ![-13, -21, -19, -5, 6]] ![![13, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![-5, -131, -77, 2, 16]] where
 M := ![![![169, 0, 0, 0, 0], ![0, 13, 0, 0, 0]], ![![-169, -273, -247, -65, 78], ![31, 53, 51, 11, -16]]]
 hmul := by decide  
 g := ![![![![13, 13, 13, 0, 0]], ![![0, 2, 1, 2, 0]]], ![![![-67, -115, -107, -25, 28]], ![![11, 17, 17, 1, -6]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-5, -131, -77, 2, 16]] ![![-1, -1, -1, 0, 0]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![-13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, 18, 12, 13, 4]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![8, 18, 12, 13, 4]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![4, 8, 1, 0, 0], ![1, 13, 0, 1, 0], ![8, 2, 0, 0, 1]] where
  M :=![![![8, 18, 12, 13, 4], ![37, 93, 66, 73, 22], ![205, 506, 357, 403, 124], ![555, 1366, 964, 1080, 330], ![1230, 3036, 2142, 2406, 737]]]
  hmulB := by decide  
  f := ![![![2, -2, 12, 9, -6]], ![![-27, -67, -74, -21, 24]], ![![-5, -18, -19, -5, 6]], ![![-30, -67, -70, -18, 22]], ![![14, 18, 22, 6, -7]]]
  g := ![![![-5, -15, 12, 13, 4], ![-28, -84, 66, 73, 22], ![-154, -461, 357, 403, 124], ![-413, -1238, 964, 1080, 330], ![-920, -2756, 2142, 2406, 737]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [15, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 16], [0, 1]]
 g := ![![[2, 8], [8], [16], [1]], ![[0, 9], [8], [16], [1]]]
 h' := ![![[4, 16], [3, 12], [2, 12], [2, 4], [0, 1]], ![[0, 1], [0, 5], [16, 5], [1, 13], [4, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [3, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [15, 13, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![119208, 301559, 208021, 251115, 84570]
  a := ![19, 19, 10, 20, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-96503, -282132, 208021, 251115, 84570]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![-3, -7, -3, -1, 1]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![-3, -7, -3, -1, 1]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![11, 15, 1, 0, 0], ![11, 4, 0, 1, 0], ![7, 8, 0, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![-3, -7, -3, -1, 1], ![5, 8, 5, 2, -3], ![-16, -33, -28, -15, 7], ![11, 19, 23, -5, -17], ![-60, -123, -105, -54, 13]]]
  hmulB := by decide  
  f := ![![![36665, 53892, 36784, 15192, -23734], ![-37434, -146574, 170, 0, 0]], ![![-36, -50, -36, -15, 24], ![51, 153, 0, 0, 0]], ![![21552, 31679, 21622, 8930, -13951], ![-22004, -86157, 100, 0, 0]], ![![23717, 34862, 23794, 9827, -15352], ![-24204, -94806, 110, 0, 0]], ![![15079, 22164, 15128, 6248, -9761], ![-15398, -60282, 70, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-11, -15, 17, 0, 0], ![-11, -4, 0, 17, 0], ![-7, -8, 0, 0, 17]], ![![2, 2, -3, -1, 1], ![-3, -3, 5, 2, -3], ![24, 23, -28, -15, 7], ![-4, -10, 23, -5, -17], ![94, 92, -105, -54, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [10, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 16], [0, 1]]
 g := ![![[6, 15], [8], [13], [1]], ![[7, 2], [8], [13], [1]]]
 h' := ![![[8, 16], [4, 7], [4, 12], [7, 8], [0, 1]], ![[0, 1], [9, 10], [15, 5], [3, 9], [8, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [6, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [10, 9, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1075, -2107, -1939, -367, 874]
  a := ![1, -3, 1, -4, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1069, 1262, -1939, -367, 874]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![-6, 1, 0, 0, 0]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![-6, 1, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![-6, 1, 0, 0, 0], ![0, -6, 1, 0, 0], ![0, 1, -6, 2, 0], ![1, 1, 0, -5, 2], ![6, 15, 12, 9, -7]]]
  hmulB := by decide  
  f := ![![![-8207, 13929, -95764, 31790, 132], ![-23443, -10132, -273020, -1122, 0]], ![![-5975, 10136, -69659, 23124, 96], ![-17067, -7361, -198594, -816, 0]], ![![-7455, 12664, -87041, 28894, 120], ![-21295, -9196, -248149, -1020, 0]], ![![-6716, 11402, -78356, 26011, 108], ![-19184, -8276, -223388, -918, 0]], ![![-6271, 10655, -73232, 24310, 101], ![-17913, -7736, -208780, -858, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-11, 17, 0, 0, 0], ![-15, 0, 17, 0, 0], ![-14, 0, 0, 17, 0], ![-13, 0, 0, 0, 17]], ![![-1, 1, 0, 0, 0], ![3, -6, 1, 0, 0], ![3, 1, -6, 2, 0], ![2, 1, 0, -5, 2], ![-22, 15, 12, 9, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![8, 18, 12, 13, 4]] ![![17, 0, 0, 0, 0], ![-3, -7, -3, -1, 1]]
  ![![17, 0, 0, 0, 0], ![-37, -22, 0, 5, -1]] where
 M := ![![![136, 306, 204, 221, 68], ![-223, -553, -391, -433, -131]]]
 hmul := by decide  
 g := ![![![![8, 18, 12, 13, 4], ![0, 0, 0, 0, 0]], ![![13, -17, -23, -29, -7], ![12, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![17, 0, 0, 0, 0], ![-37, -22, 0, 5, -1]] ![![17, 0, 0, 0, 0], ![-6, 1, 0, 0, 0]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![289, 0, 0, 0, 0], ![-102, 17, 0, 0, 0]], ![![-629, -374, 0, 85, -17], ![221, 85, -34, -34, 17]]]
 hmul := by decide  
 g := ![![![![17, 0, 0, 0, 0]], ![![-6, 1, 0, 0, 0]]], ![![![-37, -22, 0, 5, -1]], ![![13, 5, -2, -2, 1]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [18, 11, 6, 6, 14, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 13, 1, 1, 15], [8, 15, 9, 12, 7], [16, 13, 6, 16, 11], [7, 15, 3, 9, 5], [0, 1]]
 g := ![![[12, 1, 13, 15, 11], [7, 2, 0, 5, 1], [], []], ![[12, 11, 7, 16, 4, 14, 6, 2], [16, 4, 1, 6, 11, 4, 11, 3], [7, 12, 4, 7], [9, 10, 15, 16]], ![[2, 10, 17, 12, 17, 9, 0, 11], [2, 16, 10, 7, 14, 7, 7, 7], [2, 1, 6, 1], [12, 8, 14, 11]], ![[3, 1, 0, 3, 7, 18, 1, 1], [12, 5, 1, 12, 17, 2, 5, 4], [15, 13, 0, 6], [0, 1, 7, 7]], ![[10, 4, 17, 17, 8, 17, 3, 4], [8, 8, 10, 12, 7, 11, 13, 5], [8, 7, 15, 6], [11, 10, 6, 6]]]
 h' := ![![[12, 13, 1, 1, 15], [7, 1, 12, 8, 7], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[8, 15, 9, 12, 7], [5, 16, 12, 5, 16], [8, 1, 0, 9, 17], [1, 14, 6, 15, 11], [12, 13, 1, 1, 15]], ![[16, 13, 6, 16, 11], [15, 9, 0, 3, 8], [2, 17, 6, 11, 18], [0, 2, 14, 9, 18], [8, 15, 9, 12, 7]], ![[7, 15, 3, 9, 5], [9, 13, 17, 8, 11], [1, 1, 0, 14, 3], [9, 18, 15, 3, 14], [16, 13, 6, 16, 11]], ![[0, 1], [17, 18, 16, 14, 15], [17, 0, 13, 4, 18], [3, 4, 2, 11, 14], [7, 15, 3, 9, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 10, 6, 2], [], [], []]
 b := ![[], [14, 0, 8, 11, 10], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [18, 11, 6, 6, 14, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9163704384520085, 22597742459682387, 15946347629146419, 17890476981152343, 5473993962921746]
  a := ![13, 9, 10, 5, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![482300230764215, 1189354866299073, 839281454165601, 941604051639597, 288104945416934]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 2476099 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-62, -99, -39, 5, 8]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-62, -99, -39, 5, 8]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![13, 9, 20, 1, 0], ![10, 5, 20, 0, 1]] where
  M :=![![![-62, -99, -39, 5, 8], ![53, 24, -3, -1, 2], ![11, 79, 48, 11, -4], ![-33, -7, 17, 36, 12], ![75, 141, 81, 69, 19]]]
  hmulB := by decide  
  f := ![![![46, 71, 69, 9, -18]], ![![-99, -146, -145, -15, 36]], ![![201, 281, 286, 19, -66]], ![![156, 220, 223, 16, -52]], ![![182, 253, 258, 16, -59]]]
  g := ![![![-9, -8, -13, 5, 8], ![2, 1, -1, -1, 2], ![-4, 0, -4, 11, -4], ![-27, -17, -41, 36, 12], ![-44, -25, -73, 69, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [8, 14, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 19, 6], [5, 3, 17], [0, 1]]
 g := ![![[7, 20, 8], [20, 22, 3], [11, 18, 1], []], ![[11, 11, 22, 1], [14, 11, 8, 4], [14, 19, 7, 8], [2, 13]], ![[7, 20, 14, 10], [22, 0, 20, 10], [13, 7, 11, 19], [14, 13]]]
 h' := ![![[13, 19, 6], [1, 20, 13], [4, 1, 7], [0, 0, 1], [0, 1]], ![[5, 3, 17], [19, 3, 21], [7, 0, 4], [15, 17, 3], [13, 19, 6]], ![[0, 1], [5, 0, 12], [21, 22, 12], [5, 6, 19], [5, 3, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 5], []]
 b := ![[], [13, 21, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [8, 14, 5, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![80193700, 198290212, 139678250, 157589360, 48496364]
  a := ![7, 7, 3, 6, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-106670940, -63586776, -173132010, 157589360, 48496364]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![46, 71, 69, 9, -18]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![46, 71, 69, 9, -18]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![22, 6, 1, 0, 0], ![3, 5, 0, 1, 0], ![13, 19, 0, 0, 1]] where
  M :=![![![46, 71, 69, 9, -18], ![-99, -146, -145, -15, 36], ![201, 281, 286, 19, -66], ![-139, -169, -183, 6, 34], ![201, 219, 249, -27, -37]]]
  hmulB := by decide  
  f := ![![![-62, -99, -39, 5, 8]], ![![53, 24, -3, -1, 2]], ![![-45, -85, -36, 5, 8]], ![![2, -8, -5, 2, 2]], ![![12, -30, -21, 5, 7]]]
  g := ![![![-55, -2, 69, 9, -18], ![116, 5, -145, -15, 36], ![-230, -12, 286, 19, -66], ![149, 11, -183, 6, 34], ![-205, -19, 249, -27, -37]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [12, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 22], [0, 1]]
 g := ![![[17, 2], [16, 3], [1, 9], [1]], ![[0, 21], [2, 20], [5, 14], [1]]]
 h' := ![![[3, 22], [15, 18], [11, 16], [11, 3], [0, 1]], ![[0, 1], [0, 5], [13, 7], [20, 20], [3, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [7, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [12, 20, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20514, 51398, 35641, 42204, 13902]
  a := ![7, 8, 3, 9, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-46562, -27722, 35641, 42204, 13902]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-62, -99, -39, 5, 8]] ![![46, 71, 69, 9, -18]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)


lemma PB512I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB512I0 : PrimesBelowBoundCertificateInterval O 1 23 512 where
  m := 9
  g := ![5, 4, 5, 3, 2, 3, 3, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB512I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0]
    · exact ![I23N0, I23N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![9, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![49, 49, 7]
    · exact ![14641, 11]
    · exact ![2197, 13, 13]
    · exact ![289, 289, 17]
    · exact ![2476099]
    · exact ![12167, 529]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N1
      exact NI2N2
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
      exact NI7N2
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N0, I7N1, I7N2, I11N1, I13N1, I13N2, I17N0, I17N1, I17N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1, I7N2], [I11N1], [I13N1, I13N2], [I17N0, I17N1, I17N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
