
import IdealArithmetic.Examples.NF3_1_192584_1.RI3_1_192584_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39059211218934, -11722736633013, 2795720998876]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![39059211218934, -11722736633013, 2795720998876]] 
 ![![37, 0, 0], ![4, 1, 0], ![11, 0, 1]] where
  M :=![![![39059211218934, -11722736633013, 2795720998876], ![-288499115521737, 86586468199826, -20649752267150], ![1045926365714371, -313911083715137, 74863731566813]]]
  hmulB := by decide  
  f := ![![![31124988, -10188443, -3972626]], ![![13718959, -2085498, -1087568]], ![![40916443, -3308074, -2440459]]]
  g := ![![![1491816939550, -11722736633013, 2795720998876], ![-11018857118443, 86586468199826, -20649752267150], ![39947828468648, -313911083715137, 74863731566813]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1577824474, 77201081, 80216950]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-1577824474, 77201081, 80216950]] 
 ![![37, 0, 0], ![9, 1, 0], ![34, 0, 1]] where
  M :=![![![-1577824474, 77201081, 80216950], ![-7864276969, -214136324, 234619112], ![-10931801969, -1976476573, -136935243]]]
  hmulB := by decide  
  f := ![![![-493041988008129908, 147975373645914667, -35290211865151872]], ![![-21504636318303221, 6454129002635683, -1539226252964578]], ![![-809894348560830869, 243071425470618237, -57969389715809749]]]
  g := ![![![-135135419, 77201081, 80216950], ![-376056753, -214136324, 234619112], ![311142850, -1976476573, -136935243]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2459, -738, 176]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![2459, -738, 176]] 
 ![![37, 0, 0], ![23, 1, 0], ![32, 0, 1]] where
  M :=![![![2459, -738, 176], ![-18162, 5451, -1300], ![65846, -19762, 4713]]]
  hmulB := by decide  
  f := ![![![-37, 82, 24]], ![![-85, 61, 20]], ![![-278, 82, 33]]]
  g := ![![![373, -738, 176], ![-2755, 5451, -1300], ![9988, -19762, 4713]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![39059211218934, -11722736633013, 2795720998876]] ![![-1577824474, 77201081, 80216950]]
  ![![37, -82, -24]] where
 M := ![![![37, -82, -24]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, -82, -24]] ![![2459, -738, 176]]
  ![![37, 0, 0]] where
 M := ![![![-37, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18871884685188922430, -5663968294009470737, 1350783148359466432]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![18871884685188922430, -5663968294009470737, 1350783148359466432]] 
 ![![41, 0, 0], ![0, 41, 0], ![24, 0, 1]] where
  M :=![![![18871884685188922430, -5663968294009470737, 1350783148359466432], ![-139391499981596647505, 41835198207299851774, -9977153439659475042], ![505350752024199479251, -151669570080899126241, 36171229913290381037]]]
  hmulB := by decide  
  f := ![![![2817893476, -1178990923, -430434254]], ![![41434000223, -4499488842, -2788416100]], ![![4926764615, -748556669, -390461021]]]
  g := ![![![-330412460376543218, -138145568146572457, 1350783148359466432], ![2440492257810506183, 1020370687982923214, -9977153439659475042], ![-8847774777921211357, -3699257806851198201, 36171229913290381037]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [1, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 40], [0, 1]]
 g := ![![[29, 1], [4], [18], [23, 21], [1]], ![[0, 40], [4], [18], [29, 20], [1]]]
 h' := ![![[12, 40], [29, 1], [19, 2], [18, 10], [40, 12], [0, 1]], ![[0, 1], [0, 40], [2, 39], [15, 31], [20, 29], [12, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [20, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [1, 29, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-586, -123, 20]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-26, -3, 20]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2817893476, -1178990923, -430434254]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![2817893476, -1178990923, -430434254]] 
 ![![41, 0, 0], ![40, 1, 0], ![0, 0, 1]] where
  M :=![![![2817893476, -1178990923, -430434254], ![41434000223, -4499488842, -2788416100], ![134367905791, -2395041277, -5678479765]]]
  hmulB := by decide  
  f := ![![![18871884685188922430, -5663968294009470737, 1350783148359466432]], ![![15011802132340493895, -4505452037879975066, 1074492012066321518]], ![![12325628098151206811, -3699257806851198201, 882225119836350757]]]
  g := ![![![1218964156, -1178990923, -430434254], ![5400330583, -4499488842, -2788416100], ![5613891631, -2395041277, -5678479765]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![18871884685188922430, -5663968294009470737, 1350783148359466432]] ![![2817893476, -1178990923, -430434254]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [30, 10, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 40, 37], [17, 2, 6], [0, 1]]
 g := ![![[22, 39, 21], [5, 41, 17], [34, 17], [37, 2, 1], []], ![[22, 11, 6, 37], [20, 11, 3, 39], [29, 25], [7, 23, 41, 19], [22, 36]], ![[8, 5, 11, 13], [26, 21, 29, 4], [38, 24], [4, 16, 39, 11], [10, 36]]]
 h' := ![![[28, 40, 37], [22, 24, 8], [33, 10, 24], [8, 0, 24], [0, 0, 1], [0, 1]], ![[17, 2, 6], [9, 9, 1], [21, 41, 31], [17, 28, 5], [38, 37, 2], [28, 40, 37]], ![[0, 1], [41, 10, 34], [25, 35, 31], [2, 15, 14], [32, 6, 40], [17, 2, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 6], []]
 b := ![[], [21, 1, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [30, 10, 41, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![720809, -281177, 58050]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16763, -6539, 1350]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-107547024858, 32277801029, -7697837882]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-107547024858, 32277801029, -7697837882]] 
 ![![47, 0, 0], ![0, 47, 0], ![2, 29, 1]] where
  M :=![![![-107547024858, 32277801029, -7697837882], ![794363751347, -238410268852, 56857764176], ![-2879890948709, 864333970655, -206132467823]]]
  hmulB := by decide  
  f := ![![![534172, -73131, -40120]], ![![3898749, -147868, -186382]], ![![2617382, -85803, -121411]]]
  g := ![![![-1960667002, 5436491481, -7697837882], ![14481877085, -40155009148, 56857764176], ![-52502681129, 145578202926, -206132467823]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [41, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 46], [0, 1]]
 g := ![![[13, 37], [11, 7], [7, 34], [36, 21], [1]], ![[32, 10], [40, 40], [27, 13], [29, 26], [1]]]
 h' := ![![[31, 46], [19, 32], [42, 30], [28, 9], [6, 31], [0, 1]], ![[0, 1], [24, 15], [32, 17], [25, 38], [27, 16], [31, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [8, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [41, 16, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-162301, -180954, 81446]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6919, -54104, 81446]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![534172, -73131, -40120]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![534172, -73131, -40120]] 
 ![![47, 0, 0], ![35, 1, 0], ![46, 0, 1]] where
  M :=![![![534172, -73131, -40120], ![3898749, -147868, -186382], ![8884889, 401693, -220999]]]
  hmulB := by decide  
  f := ![![![-107547024858, 32277801029, -7697837882]], ![![-63186853589, 18964101429, -4522692802]], ![![-166533065791, 49981123787, -11919851285]]]
  g := ![![![105091, -73131, -40120], ![375483, -147868, -186382], ![106204, 401693, -220999]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-107547024858, 32277801029, -7697837882]] ![![534172, -73131, -40120]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22577, 6776, -1616]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-22577, 6776, -1616]] 
 ![![53, 0, 0], ![0, 53, 0], ![2, 37, 1]] where
  M :=![![![-22577, 6776, -1616], ![166760, -50049, 11936], ![-604568, 181448, -43273]]]
  hmulB := by decide  
  f := ![![![-133, 40, 16]], ![![-1544, 139, 96]], ![![-1170, 99, 71]]]
  g := ![![![-365, 1256, -1616], ![2696, -9277, 11936], ![-9774, 33633, -43273]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [47, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 52], [0, 1]]
 g := ![![[23, 44], [37], [8, 4], [52], [32, 1]], ![[0, 9], [37], [30, 49], [52], [11, 52]]]
 h' := ![![[32, 52], [35, 37], [48, 14], [23, 2], [33, 23], [0, 1]], ![[0, 1], [0, 16], [19, 39], [34, 51], [27, 30], [32, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [15, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [47, 21, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-25, -1178, 332]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13, -254, 332]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![133, -40, -16]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![133, -40, -16]] 
 ![![53, 0, 0], ![31, 1, 0], ![50, 0, 1]] where
  M :=![![![133, -40, -16], ![1544, -139, -96], ![4616, -24, -179]]]
  hmulB := by decide  
  f := ![![![22577, -6776, 1616]], ![![10059, -3019, 720]], ![![32706, -9816, 2341]]]
  g := ![![![41, -40, -16], ![201, -139, -96], ![270, -24, -179]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-22577, 6776, -1616]] ![![133, -40, -16]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [30, 26, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 56, 14], [39, 2, 45], [0, 1]]
 g := ![![[45, 57, 20], [48, 25, 20], [53, 12], [20, 13, 51], [1]], ![[21, 14, 41, 43], [35, 43, 20, 40], [31, 12], [23, 6, 36, 31], [20, 33, 29, 30]], ![[12, 3, 57, 27], [28, 22, 35, 48], [50, 48], [20, 44, 14, 16], [14, 0, 32, 29]]]
 h' := ![![[7, 56, 14], [35, 56, 16], [44, 55, 16], [49, 49, 22], [29, 33, 46], [0, 1]], ![[39, 2, 45], [24, 1, 49], [26, 4, 35], [37, 19, 22], [38, 55, 23], [7, 56, 14]], ![[0, 1], [10, 2, 53], [39, 0, 8], [51, 50, 15], [17, 30, 49], [39, 2, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 9], []]
 b := ![[], [3, 19, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [30, 26, 13, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11092, 7670, -354]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-188, 130, -6]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7014, 2105, -502]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-7014, 2105, -502]] 
 ![![61, 0, 0], ![0, 61, 0], ![13, 37, 1]] where
  M :=![![![-7014, 2105, -502], ![51803, -15548, 3708], ![-187813, 56367, -13443]]]
  hmulB := by decide  
  f := ![![![-48, -21, -4]], ![![375, -116, -46]], ![![254, -78, -31]]]
  g := ![![![-8, 339, -502], ![59, -2504, 3708], ![-214, 9078, -13443]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [52, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 60], [0, 1]]
 g := ![![[23, 27], [45], [55, 48], [52, 15], [24, 1]], ![[0, 34], [45], [48, 13], [46, 46], [48, 60]]]
 h' := ![![[24, 60], [27, 37], [7, 17], [41, 32], [33, 36], [0, 1]], ![[0, 1], [0, 24], [49, 44], [16, 29], [43, 25], [24, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [12, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [52, 37, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11164, 2348, 1112]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-420, -636, 1112]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-48, -21, -4]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-48, -21, -4]] 
 ![![61, 0, 0], ![47, 1, 0], ![55, 0, 1]] where
  M :=![![![-48, -21, -4], ![375, -116, -46], ![2243, -193, -137]]]
  hmulB := by decide  
  f := ![![![-7014, 2105, -502]], ![![-4555, 1367, -326]], ![![-9403, 2822, -673]]]
  g := ![![![19, -21, -4], ![137, -116, -46], ![309, -193, -137]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-7014, 2105, -502]] ![![-48, -21, -4]]
  ![![61, 0, 0]] where
 M := ![![![61, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![58963471092885050192, -17696548932229849823, 4220397933204747602]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![58963471092885050192, -17696548932229849823, 4220397933204747602]] 
 ![![67, 0, 0], ![0, 67, 0], ![56, 65, 1]] where
  M :=![![![58963471092885050192, -17696548932229849823, 4220397933204747602], ![-435515944319499862421, 130710235957365759426, -31172699931254952044], ![1578922029029360480795, -473877647109302098673, 113013687025135909603]]]
  hmulB := by decide  
  f := ![![![-1399848802, -2039859431, -510380720]], ![![48487831849, -10076321042, -4590099582]], ![![49196854186, -11685746219, -5060507069]]]
  g := ![![![-2647444972635534560, -4358543501351320059, 4220397933204747602], ![19554555997474290329, 32193070619237875258, -31172699931254952044], ![-70893200662361947119, -116712944831987107804, 113013687025135909603]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [31, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 66], [0, 1]]
 g := ![![[61, 21], [61, 64], [37], [17], [24], [1]], ![[14, 46], [39, 3], [37], [17], [24], [1]]]
 h' := ![![[52, 66], [52, 50], [1, 8], [64, 29], [16, 34], [36, 52], [0, 1]], ![[0, 1], [39, 17], [15, 59], [31, 38], [42, 33], [60, 15], [52, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [37, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [31, 15, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1427, -642, 120]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-79, -126, 120]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1399848802, -2039859431, -510380720]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-1399848802, -2039859431, -510380720]] 
 ![![67, 0, 0], ![3, 1, 0], ![63, 0, 1]] where
  M :=![![![-1399848802, -2039859431, -510380720], ![48487831849, -10076321042, -4590099582], ![222871693189, -13752000807, -12116180473]]]
  hmulB := by decide  
  f := ![![![58963471092885050192, -17696548932229849823, 4220397933204747602]], ![![-3860082552848428535, 1158516256129495671, -276291136293144914]], ![![79009264296733114073, -23712839251340039366, 5655205325627388187]]]
  g := ![![![550353953, -2039859431, -510380720], ![5490941323, -10076321042, -4590099582], ![15335030827, -13752000807, -12116180473]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![58963471092885050192, -17696548932229849823, 4220397933204747602]] ![![-1399848802, -2039859431, -510380720]]
  ![![67, 0, 0]] where
 M := ![![![67, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10109327085827447, -3034085309605346, 723590086341868]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![10109327085827447, -3034085309605346, 723590086341868]] 
 ![![71, 0, 0], ![0, 71, 0], ![32, 43, 1]] where
  M :=![![![10109327085827447, -3034085309605346, 723590086341868], ![-74669503857450278, 22410358553639203, -5344580532868824], ![270707252110912666, -81246643803307470, 19376273244033857]]]
  hmulB := by decide  
  f := ![![![-52884779, -25435978, -5041100]], ![![473632922, -138583479, -55913056]], ![![301390840, -98574189, -38445015]]]
  g := ![![![-183740220804399, -480964211581770, 723590086341868], ![1357141875976790, 3552497485450685, -5344580532868824], ![-4920190023917898, -12879244976010751, 19376273244033857]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [62, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 70], [0, 1]]
 g := ![![[44, 36], [8, 54], [29, 38], [64], [48], [1]], ![[29, 35], [21, 17], [25, 33], [64], [48], [1]]]
 h' := ![![[41, 70], [1, 65], [48, 14], [51, 40], [16, 8], [9, 41], [0, 1]], ![[0, 1], [39, 6], [54, 57], [58, 31], [60, 63], [57, 30], [41, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [25, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [62, 30, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1321, -486, 418]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-207, -260, 418]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-52884779, -25435978, -5041100]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-52884779, -25435978, -5041100]] 
 ![![71, 0, 0], ![55, 1, 0], ![50, 0, 1]] where
  M :=![![![-52884779, -25435978, -5041100], ![473632922, -138583479, -55913056], ![2724846922, -225726526, -164019457]]]
  hmulB := by decide  
  f := ![![![10109327085827447, -3034085309605346, 723590086341868]], ![![6779485716381117, -2034708922178237, 485251749520196]], ![![10932022625384296, -3280998722303870, 782475740297567]]]
  g := ![![![22509141, -25435978, -5041100], ![153399677, -138583479, -55913056], ![328743362, -225726526, -164019457]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![10109327085827447, -3034085309605346, 723590086341868]] ![![-52884779, -25435978, -5041100]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-331371312899, 99453586174, -23718393408]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-331371312899, 99453586174, -23718393408]] 
 ![![73, 0, 0], ![0, 73, 0], ![33, 53, 1]] where
  M :=![![![-331371312899, 99453586174, -23718393408], ![2447574533566, -734584000835, 175188778940], ![-8873450901498, 2663165094686, -635130414661]]]
  hmulB := by decide  
  f := ![![![-1336015, 23738, 56440]], ![![-5563822, -376535, 103916]], ![![-4707331, -288815, 96127]]]
  g := ![![![6182680405, 18582581326, -23718393408], ![-45666509198, -137254647735, 175188778940], ![165559627155, 497603795503, -635130414661]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [49, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 72], [0, 1]]
 g := ![![[17, 3], [41], [50], [72, 24], [24], [1]], ![[0, 70], [41], [50], [9, 49], [24], [1]]]
 h' := ![![[43, 72], [27, 52], [24, 48], [49, 59], [57, 30], [24, 43], [0, 1]], ![[0, 1], [0, 21], [44, 25], [31, 14], [33, 43], [48, 30], [43, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [18, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [49, 30, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1101, -1025, 325]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-162, -250, 325]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1336015, 23738, 56440]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-1336015, 23738, 56440]] 
 ![![73, 0, 0], ![39, 1, 0], ![43, 0, 1]] where
  M :=![![![-1336015, 23738, 56440], ![-5563822, -376535, 103916], ![-4664102, -1910494, -352797]]]
  hmulB := by decide  
  f := ![![![-331371312899, 99453586174, -23718393408]], ![![-143505570815, 43069943287, -10271624164]], ![![-316745443235, 95063963016, -22671525085]]]
  g := ![![![-64229, 23738, 56440], ![63735, -376535, 103916], ![1164595, -1910494, -352797]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-331371312899, 99453586174, -23718393408]] ![![-1336015, 23738, 56440]]
  ![![73, 0, 0]] where
 M := ![![![73, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![428528079053220245, -128612986638007618, 30672533106258138]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![428528079053220245, -128612986638007618, 30672533106258138]] 
 ![![79, 0, 0], ![23, 1, 0], ![52, 0, 1]] where
  M :=![![![428528079053220245, -128612986638007618, 30672533106258138], ![-3165193764157563280, 949961141859608591, -226553440169757098], ![11475111819806170524, -3443994630202713164, 821348155221600973]]]
  hmulB := by decide  
  f := ![![![-282279029, 1575483682, 445109006]], ![![-620034501, 550894921, 175108652]], ![![-2391150168, 1145049428, 405135773]]]
  g := ![![![22679177850657877, -128612986638007618, 30672533106258138], ![-167512925798749263, 949961141859608591, -226553440169757098], ![607302332189181300, -3443994630202713164, 821348155221600973]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![49079, -30784, -10324]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![49079, -30784, -10324]] 
 ![![79, 0, 0], ![26, 1, 0], ![18, 0, 1]] where
  M :=![![![49079, -30784, -10324], ![991292, -126429, -71892], ![3470900, -100044, -157213]]]
  hmulB := by decide  
  f := ![![![12683919129, -3806790736, 907870332]], ![![2988556250, -896947397, 213910348]], ![![7189368906, -2157726068, 514589747]]]
  g := ![![![13105, -30784, -10324], ![70538, -126429, -71892], ![112682, -100044, -157213]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![46483, 2066, -1166]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![46483, 2066, -1166]] 
 ![![79, 0, 0], ![29, 1, 0], ![54, 0, 1]] where
  M :=![![![46483, 2066, -1166], ![117500, 26661, 2966], ![-156728, 82928, 28727]]]
  hmulB := by decide  
  f := ![![![-519926099, 156044030, -37214482]], ![![-142247837, 42692463, -10181600]], ![![-531627526, 159555948, -38052029]]]
  g := ![![![627, 2066, -1166], ![-10327, 26661, 2966], ![-52062, 82928, 28727]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![428528079053220245, -128612986638007618, 30672533106258138]] ![![49079, -30784, -10324]]
  ![![519926099, -156044030, 37214482]] where
 M := ![![![519926099, -156044030, 37214482]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![519926099, -156044030, 37214482]] ![![46483, 2066, -1166]]
  ![![79, 0, 0]] where
 M := ![![![-79, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB125I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB125I1 : PrimesBelowBoundCertificateInterval O 31 79 125 where
  m := 11
  g := ![3, 2, 1, 2, 2, 1, 2, 2, 2, 2, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB125I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![37, 37, 37]
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![79, 79, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
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
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
  β := ![I37N0, I37N1, I37N2, I41N1, I47N1, I53N1, I61N1, I67N1, I71N1, I73N1, I79N0, I79N1, I79N2]
  Il := ![[I37N0, I37N1, I37N2], [I41N1], [], [I47N1], [I53N1], [], [I61N1], [I67N1], [I71N1], [I73N1], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
