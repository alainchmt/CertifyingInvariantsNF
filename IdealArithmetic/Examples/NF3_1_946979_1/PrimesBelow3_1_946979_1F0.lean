
import IdealArithmetic.Examples.NF3_1_946979_1.RI3_1_946979_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-85512595029159, -5563029583497, -5289885442487]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-85512595029159, -5563029583497, -5289885442487]] 
 ![![2, 0, 0], ![0, 2, 0], ![1, 1, 1]] where
  M :=![![![-85512595029159, -5563029583497, -5289885442487], ![-989208577745069, -64353053259211, -61193325418467], ![-1040286532113939, -67675934188291, -64353053259211]]]
  hmulB := by decide  
  f := ![![![-4886312, -239425, 629329]], ![![117684523, -7403628, -2633675]], ![![34012868, 2006620, -4703987]]]
  g := ![![![-40111354793336, -136572070505, -5289885442487], ![-464007626163301, -1579863920372, -61193325418467], ![-487966739427364, -1661440464540, -64353053259211]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1], [0, 1]]
 g := ![![[1]], ![[1]]]
 h' := ![![[1, 1], [0, 1]], ![[0, 1], [1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], []]
 b := ![[], [1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2243, 203, 5]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1124, 99, 5]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4886312, 239425, -629329]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![4886312, 239425, -629329]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![4886312, 239425, -629329], ![-117684523, 7403628, 2633675], ![44772475, -11656293, 7403628]]]
  hmulB := by decide  
  f := ![![![85512595029159, 5563029583497, 5289885442487]], ![![537360586387114, 34958041421354, 33241605430477]], ![![562899563571549, 36619481885894, 34821469350849]]]
  g := ![![![2638108, 239425, -629329], ![-63860913, 7403628, 2633675], ![24512570, -11656293, 7403628]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-85512595029159, -5563029583497, -5289885442487]] ![![4886312, 239425, -629329]]
  ![![2, 0, 0]] where
 M := ![![![-2, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0)
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0]] 
 ![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [1, 2, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 1, 2], [0, 1, 1], [0, 1]]
 g := ![![[1]], ![[2, 1, 1, 2]], ![[0, 2, 2, 1]]]
 h' := ![![[2, 1, 2], [0, 1]], ![[0, 1, 1], [2, 1, 2]], ![[0, 1], [0, 1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 2], []]
 b := ![[], [2, 2, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [1, 2, 1, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-190107, 6966, -12822]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-63369, 2322, -4274]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 27 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def PBC3 : ContainsPrimesAboveP 3 ![I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![3, 0, 0]]) timesTableT_eq_Table B_one_repr 3 (by decide) 𝕀

instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0]] 
 ![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [3, 2, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 0, 2], [3, 4, 3], [0, 1]]
 g := ![![[2, 2, 1], []], ![[1, 2, 1, 2], [3, 4]], ![[4, 2], [2, 4]]]
 h' := ![![[4, 0, 2], [0, 0, 1], [0, 1]], ![[3, 4, 3], [2, 2, 4], [4, 0, 2]], ![[0, 1], [3, 3], [3, 4, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 4], []]
 b := ![[], [4, 3, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [3, 2, 3, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-110695, 3450, 4830]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-22139, 690, 966]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 125 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def PBC5 : ContainsPrimesAboveP 5 ![I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![5, 0, 0]]) timesTableT_eq_Table B_one_repr 5 (by decide) 𝕀

instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0]] 
 ![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [6, 3, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 1, 6], [5, 5, 1], [0, 1]]
 g := ![![[3, 2, 1], [1]], ![[5, 6, 0, 6], [1, 4, 2, 6]], ![[2, 0, 5, 4], [2, 5, 2, 1]]]
 h' := ![![[3, 1, 6], [1, 4, 1], [0, 1]], ![[5, 5, 1], [0, 0, 1], [3, 1, 6]], ![[0, 1], [1, 3, 5], [5, 5, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 6], []]
 b := ![[], [4, 5, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [6, 3, 6, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-742, -378, -406]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-106, -54, -58]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀


def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-191316, 330645, -298684]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-191316, 330645, -298684]] 
 ![![11, 0, 0], ![0, 1, 0], ![4, 0, 1]] where
  M :=![![![-191316, 330645, -298684], ![-55853908, 1003420, 3637095], ![61830615, -6400208, 1003420]]]
  hmulB := by decide  
  f := ![![![-24285016212160, -1579863920372, -1502292775555]], ![![-25538977184435, -1661440464540, -1579863920372]], ![![-35688601632564, -2321725198585, -2207728746560]]]
  g := ![![![91220, 330645, -298684], ![-6400208, 1003420, 3637095], ![5256085, -6400208, 1003420]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![134310945636046359025789240, 8737610684203925707807435, 8308594960128553871278884]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![134310945636046359025789240, 8737610684203925707807435, 8308594960128553871278884]] 
 ![![11, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![134310945636046359025789240, 8737610684203925707807435, 8308594960128553871278884], ![1553707257544039573929151308, 101076565795532143540673704, 96113717526243182785881785], ![1633933197946134107359990345, 106295671585369712980511288, 101076565795532143540673704]]]
  hmulB := by decide  
  f := ![![![-36899029009464, 2180157853352, 960024805139]], ![![16320421687363, -3703557111820, 2180157853352]], ![![37062683506984, 690890024905, -3703557111820]]]
  g := ![![![12210085966913305365980840, 8737610684203925707807435, 8308594960128553871278884], ![141246114322185415811741028, 101076565795532143540673704, 96113717526243182785881785], ![148539381631466737032726395, 106295671585369712980511288, 101076565795532143540673704]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-191316, 330645, -298684]] ![![-191316, 330645, -298684]]
  ![![-36899029009464, 2180157853352, 960024805139]] where
 M := ![![![-36899029009464, 2180157853352, 960024805139]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI11N1 : IdealMulLeCertificate' Table 
  ![![-36899029009464, 2180157853352, 960024805139]] ![![134310945636046359025789240, 8737610684203925707807435, 8308594960128553871278884]]
  ![![11, 0, 0]] where
 M := ![![![11, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1910965, -124318, -118214]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-1910965, -124318, -118214]] 
 ![![13, 0, 0], ![0, 13, 0], ![6, 5, 1]] where
  M :=![![![-1910965, -124318, -118214], ![-22106018, -1438109, -1367498], ![-23247466, -1512366, -1438109]]]
  hmulB := by decide  
  f := ![![![-1201, 26, 74]], ![![13838, -1497, 286]], ![![5142, -475, 29]]]
  g := ![![![-92437, 35904, -118214], ![-1069310, 415337, -1367498], ![-1124524, 436783, -1438109]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [2, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 12], [0, 1]]
 g := ![![[], [4], [0, 1]], ![[], [4], [0, 12]]]
 h' := ![![[0, 12], [5], [0, 11], [0, 1]], ![[0, 1], [5], [0, 2], [0, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [0, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [2, 0, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7109, -97, 3969]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1285, -1534, 3969]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1201, 26, 74]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-1201, 26, 74]] 
 ![![13, 0, 0], ![10, 1, 0], ![11, 0, 1]] where
  M :=![![![-1201, 26, 74], ![13838, -1497, 286], ![4862, 1154, -1497]]]
  hmulB := by decide  
  f := ![![![-1910965, -124318, -118214]], ![![-3170436, -206253, -196126]], ![![-3405237, -221528, -210651]]]
  g := ![![![-175, 26, 74], ![1974, -1497, 286], ![753, 1154, -1497]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-1910965, -124318, -118214]] ![![-1201, 26, 74]]
  ![![13, 0, 0]] where
 M := ![![![13, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35688601632564, -2321725198585, -2207728746560]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-35688601632564, -2321725198585, -2207728746560]] 
 ![![17, 0, 0], ![0, 17, 0], ![4, 0, 1]] where
  M :=![![![-35688601632564, -2321725198585, -2207728746560], ![-412845275606720, -26857686646324, -25538977184435], ![-434162612135395, -28244487897180, -26857686646324]]]
  hmulB := by decide  
  f := ![![![-5077628, 91220, 330645]], ![![61830615, -6400208, 1003420]], ![![-191316, 330645, -298684]]]
  g := ![![![-1579863920372, -136572070505, -2207728746560], ![-18275845109940, -1579863920372, -25538977184435], ![-19219521502947, -1661440464540, -26857686646324]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [14, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 16], [0, 1]]
 g := ![![[2, 4], [9], [2], [1]], ![[9, 13], [9], [2], [1]]]
 h' := ![![[6, 16], [14, 15], [15, 14], [3, 6], [0, 1]], ![[0, 1], [2, 2], [14, 3], [5, 11], [6, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [15, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [14, 11, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1118, 68, 86]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-86, 4, 86]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5077628, 91220, 330645]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-5077628, 91220, 330645]] 
 ![![17, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-5077628, 91220, 330645], ![61830615, -6400208, 1003420], ![17058140, 5256085, -6400208]]]
  hmulB := by decide  
  f := ![![![-35688601632564, -2321725198585, -2207728746560]], ![![-24285016212160, -1579863920372, -1502292775555]], ![![-25538977184435, -1661440464540, -1579863920372]]]
  g := ![![![-298684, 91220, 330645], ![3637095, -6400208, 1003420], ![1003420, 5256085, -6400208]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-35688601632564, -2321725198585, -2207728746560]] ![![-5077628, 91220, 330645]]
  ![![17, 0, 0]] where
 M := ![![![17, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1005973604337148523, -65443703576489408, -62230424925061416]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-1005973604337148523, -65443703576489408, -62230424925061416]] 
 ![![19, 0, 0], ![12, 1, 0], ![18, 0, 1]] where
  M :=![![![-1005973604337148523, -65443703576489408, -62230424925061416], ![-11637089460986484792, -757051904636902859, -719880739341383488], ![-12237972568803519296, -796142409420086440, -757051904636902859]]]
  hmulB := by decide  
  f := ![![![2346328839, 109618432, -297106760]], ![![-1442264108, 255272477, -124183072]], ![![3301713994, -185060888, -95429779]]]
  g := ![![![47342025643780519, -65443703576489408, -62230424925061416], ![547651931726381700, -757051904636902859, -719880739341383488], ![575930033036935234, -796142409420086440, -757051904636902859]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27231, 4350, -1898]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-27231, 4350, -1898]] 
 ![![19, 0, 0], ![13, 1, 0], ![14, 0, 1]] where
  M :=![![![-27231, 4350, -1898], ![-354926, -19639, 47850], ![813450, -49666, -19639]]]
  hmulB := by decide  
  f := ![![![-2762208421, -179695718, -170872678]], ![![-3571678961, -232355897, -220947248]], ![![-3803895640, -247462774, -235312379]]]
  g := ![![![-3011, 4350, -1898], ![-40501, -19639, 47850], ![91266, -49666, -19639]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-1005973604337148523, -65443703576489408, -62230424925061416]] ![![-27231, 4350, -1898]]
  ![![2762208421, 179695718, 170872678]] where
 M := ![![![2762208421, 179695718, 170872678]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![2762208421, 179695718, 170872678]] ![![-27231, 4350, -1898]]
  ![![19, 0, 0]] where
 M := ![![![-19, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8794, -84, -643]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![8794, -84, -643]] 
 ![![23, 0, 0], ![8, 1, 0], ![13, 0, 1]] where
  M :=![![![8794, -84, -643], ![-120241, 11366, -924], ![-15708, -10595, 11366]]]
  hmulB := by decide  
  f := ![![![119396176, 7767329, 7385954]], ![![101580122, 6608304, 6283837]], ![![130636557, 8498573, 8081294]]]
  g := ![![![775, -84, -643], ![-8659, 11366, -924], ![-3422, -10595, 11366]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3930876639698, 515139386226, -166724101519]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-3930876639698, 515139386226, -166724101519]] 
 ![![23, 0, 0], ![19, 1, 0], ![9, 0, 1]] where
  M :=![![![-3930876639698, 515139386226, -166724101519], ![-31177406984053, -3263980233622, 5666533248486], ![96331065224262, -4894867270727, -3263980233622]]]
  hmulB := by decide  
  f := ![![![38390495101975593824108206, 2497497121968551973824885, 2374870287827896318682018]], ![![51022615250493604097895360, 3319280837742021567480563, 3156304513494960946392699]], ![![35328105118517372327053363, 2298273065344217273335597, 2185428110483264148587752]]]
  g := ![![![-531217741927, 515139386226, -166724101519], ![-876547033983, -3263980233622, 5666533248486], ![9509102846551, -4894867270727, -3263980233622]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![8794, -84, -643]] ![![-3930876639698, 515139386226, -166724101519]]
  ![![-93890101922044226, 7951709757173153, 156578748588036]] where
 M := ![![![-93890101922044226, 7951709757173153, 156578748588036]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![-93890101922044226, 7951709757173153, 156578748588036]] ![![-3930876639698, 515139386226, -166724101519]]
  ![![23, 0, 0]] where
 M := ![![![136240114668742710647382684071, -75087145139485779180318803414, 60201300665415749323194729260]]]
 hmul := by decide  
 g := ![![![![5923483246467074375973160177, -3264658484325468660013861018, 2617447855018076057530205620]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0]] 
 ![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [27, 1, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 14, 21], [1, 14, 8], [0, 1]]
 g := ![![[6, 12, 5], [27, 13], [6, 25, 24], [1]], ![[9, 2, 17, 2], [4, 28], [25, 25, 10, 11], [25, 4, 5, 10]], ![[0, 15, 19, 26], [3, 4], [0, 3], [3, 25, 6, 19]]]
 h' := ![![[12, 14, 21], [24, 20, 11], [12, 19, 10], [2, 28, 13], [0, 1]], ![[1, 14, 8], [28, 1, 23], [7, 15, 17], [9, 28, 16], [12, 14, 21]], ![[0, 1], [0, 8, 24], [20, 24, 2], [7, 2], [1, 14, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 23], []]
 b := ![[], [8, 19, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [27, 1, 16, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![30508, 1015, 2030]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1052, 35, 70]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0]] 
 ![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [17, 8, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 10, 9], [26, 20, 22], [0, 1]]
 g := ![![[24, 21, 10], [20, 10, 18], [6, 28, 7], [1]], ![[12, 4, 13, 1], [23, 18, 23, 18], [8, 12, 21, 7], [13, 16, 7, 16]], ![[18, 14, 24, 24], [1, 28, 12, 22], [25, 24, 15, 12], [19, 6, 29, 15]]]
 h' := ![![[26, 10, 9], [1, 30, 17], [22, 13, 24], [14, 23, 21], [0, 1]], ![[26, 20, 22], [4, 18, 21], [18, 20, 8], [26, 2, 7], [26, 10, 9]], ![[0, 1], [10, 14, 24], [21, 29, 30], [17, 6, 3], [26, 20, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 9], []]
 b := ![[], [23, 18, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [17, 8, 10, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2061407, 156240, -31248]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-66497, 5040, -1008]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀



lemma PB276I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB276I0 : PrimesBelowBoundCertificateInterval O 1 31 276 where
  m := 11
  g := ![2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB276I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0]
    · exact ![I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1, I19N1]
    · exact ![I23N0, I23N1, I23N1]
    · exact ![I29N0]
    · exact ![I31N0]
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
    · exact PBC29
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![4, 2]
    · exact ![27]
    · exact ![125]
    · exact ![343]
    · exact ![11, 11, 11]
    · exact ![169, 13]
    · exact ![289, 17]
    · exact ![19, 19, 19]
    · exact ![23, 23, 23]
    · exact ![24389]
    · exact ![29791]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
  β := ![I2N0, I2N1, I3N0, I5N0, I11N0, I11N1, I13N0, I13N1, I17N1, I19N0, I19N1, I23N0, I23N1]
  Il := ![[I2N0, I2N1], [I3N0], [I5N0], [], [I11N0, I11N0, I11N1], [I13N0, I13N1], [I17N1], [I19N0, I19N1, I19N1], [I23N0, I23N1, I23N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
