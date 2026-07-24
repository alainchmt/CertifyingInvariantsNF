
import IdealArithmetic.Examples.NF3_1_390104_1.RI3_1_390104_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-451625, 245066, -78873]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-451625, 245066, -78873]] 
 ![![37, 0, 0], ![0, 37, 0], ![30, 35, 1]] where
  M :=![![![-451625, 245066, -78873], ![-8045046, 1196261, 577452], ![16951686, -7301298, 1773713]]]
  hmulB := by decide  
  f := ![![![171296562697, 3816176408, 6374771505]], ![![650226693510, 14485870169, 24198072234]], ![![782062374078, 17422929769, 29104313939]]]
  g := ![![![51745, 81233, -78873], ![-685638, -513907, 577452], ![-979992, -1875169, 1773713]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [32, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 36], [0, 1]]
 g := ![![[4, 28], [30], [19, 11], [30], [1]], ![[9, 9], [30], [17, 26], [30], [1]]]
 h' := ![![[20, 36], [36, 19], [21, 17], [27, 23], [5, 20], [0, 1]], ![[0, 1], [9, 18], [28, 20], [6, 14], [35, 17], [20, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [30, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [32, 17, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![848, 496, -433]
  a := ![0, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![374, 423, -433]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![171296562697, 3816176408, 6374771505]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![171296562697, 3816176408, 6374771505]] 
 ![![37, 0, 0], ![4, 1, 0], ![33, 0, 1]] where
  M :=![![![171296562697, 3816176408, 6374771505], ![650226693510, 14485870169, 24198072234], ![1039476687126, 23157653298, 38683942403]]]
  hmulB := by decide  
  f := ![![![-451625, 245066, -78873]], ![![-266258, 58825, 7080]], ![![55353, 21240, -22408]]]
  g := ![![![-1468529800, 3816176408, 6374771505], ![-5574410024, 14485870169, 24198072234], ![-8911460145, 23157653298, 38683942403]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-451625, 245066, -78873]] ![![171296562697, 3816176408, 6374771505]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1499703428655871664485840191851683859, -121357773278564418487027446653060426, -171224598826837263300700591883679733]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![1499703428655871664485840191851683859, -121357773278564418487027446653060426, -171224598826837263300700591883679733]] 
 ![![41, 0, 0], ![0, 41, 0], ![27, 34, 1]] where
  M :=![![![1499703428655871664485840191851683859, -121357773278564418487027446653060426, -171224598826837263300700591883679733], ![-17464909080337400856671460372135332766, 5730451573778530402189681843713057877, -706522517489367782062483523726540744], ![-29843401954750971542348259930747496218, -169456220197524695723951934232784970, 5023929056289162620127198319986517133]]]
  hmulB := by decide  
  f := ![![![699259939801603199714600864879709362101277497091135667585397383492324121, 15578241870799162431135637650878577054437857905444362579504628372421748, 26022835885622496715302638578658835219081819817872747259183015857168385]], ![![2654329260333494664960869135023201192346345621423020220436667617431175270, 59133636675864116116201901341018739788875963556745370785500374547861133, 98780397383642480724012190109953401601477213352078582256879916831602014]], ![![2765134711149685713021962880925702667522176845795651115199965074594412293, 61602180939828838441944367145442241900696807106521588905141973296916456, 102904002780857520799263409678370154798921647950294144531078997360914098]]]
  g := ![![![149335795048304335941579418846610650, 139031185044729330091141284814440256, -171224598826837263300700591883679733], ![39297533948183640463794994353201642, 725663833376025243714978576839401053, -706522517489367782062483523726540744], ![-4036328938403862494775185721228864849, -4170318149610464726342651093018887012, 5023929056289162620127198319986517133]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [19, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 40], [0, 1]]
 g := ![![[32, 25], [2], [18], [36, 8], [1]], ![[2, 16], [2], [18], [10, 33], [1]]]
 h' := ![![[7, 40], [2, 36], [32, 17], [13, 10], [22, 7], [0, 1]], ![[0, 1], [8, 5], [28, 24], [1, 31], [30, 34], [7, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [21, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [19, 34, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![700, 1785, -911]
  a := ![-1, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![617, 799, -911]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-699259939801603199714600864879709362101277497091135667585397383492324121, -15578241870799162431135637650878577054437857905444362579504628372421748, -26022835885622496715302638578658835219081819817872747259183015857168385]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-699259939801603199714600864879709362101277497091135667585397383492324121, -15578241870799162431135637650878577054437857905444362579504628372421748, -26022835885622496715302638578658835219081819817872747259183015857168385]] 
 ![![41, 0, 0], ![19, 1, 0], ![9, 0, 1]] where
  M :=![![![-699259939801603199714600864879709362101277497091135667585397383492324121, -15578241870799162431135637650878577054437857905444362579504628372421748, -26022835885622496715302638578658835219081819817872747259183015857168385], ![-2654329260333494664960869135023201192346345621423020220436667617431175270, -59133636675864116116201901341018739788875963556745370785500374547861133, -98780397383642480724012190109953401601477213352078582256879916831602014], ![-4243309931155009232936704175412816051899007127778345203546139711418193566, -94533241042025042528192190794773184636964166991044748757183204490908978, -157914034059506596840214091450972141390353176908823953042380291379463147]]]
  hmulB := by decide  
  f := ![![![-1499703428655871664485840191851683859, 121357773278564418487027446653060426, 171224598826837263300700591883679733]], ![![-269011123515223433379500079830406355, -83528143450873328071613667251339263, 96580241346323799628677921207718431]], ![![398684660898734794194529224489813207, 30772589748892791758712169612447044, -84948967484088469522460804708131696]]]
  g := ![![![-4123605397215040075251219568416753197444434598215562274199080529312084, -15578241870799162431135637650878577054437857905444362579504628372421748, -26022835885622496715302638578658835219081819817872747259183015857168385], ![-15652843586324247127729836550104012730351399845759778907322957305790137, -59133636675864116116201901341018739788875963556745370785500374547861133, -98780397383642480724012190109953401601477213352078582256879916831602014], ![-25023220605389611057051847006179909055695350311440960970200883016481821, -94533241042025042528192190794773184636964166991044748757183204490908978, -157914034059506596840214091450972141390353176908823953042380291379463147]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![1499703428655871664485840191851683859, -121357773278564418487027446653060426, -171224598826837263300700591883679733]] ![![-699259939801603199714600864879709362101277497091135667585397383492324121, -15578241870799162431135637650878577054437857905444362579504628372421748, -26022835885622496715302638578658835219081819817872747259183015857168385]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [35, 35, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 39, 33], [37, 3, 10], [0, 1]]
 g := ![![[26, 36, 9], [21, 24, 13], [29, 35], [5, 30, 1], []], ![[3, 7, 21, 22], [4, 9, 35, 33], [17, 10], [6, 15, 24, 39], [27, 14]], ![[32, 8, 41, 14], [8, 23, 25, 24], [25, 16], [13, 29, 7, 31], [7, 14]]]
 h' := ![![[36, 39, 33], [39, 4, 3], [26, 36, 20], [40, 22, 11], [0, 0, 1], [0, 1]], ![[37, 3, 10], [32, 18, 12], [0, 11, 1], [6, 8, 28], [7, 40, 3], [36, 39, 33]], ![[0, 1], [33, 21, 28], [16, 39, 22], [17, 13, 4], [6, 3, 39], [37, 3, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 22], []]
 b := ![[], [39, 23, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [35, 35, 13, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-235683, -5805, -9116]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5481, -135, -212]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6811836101629, 1807405810024, -8061165702]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-6811836101629, 1807405810024, -8061165702]] 
 ![![47, 0, 0], ![0, 47, 0], ![44, 35, 1]] where
  M :=![![![-6811836101629, 1807405810024, -8061165702], ![-822238901604, -8425773934805, 5406095098668], ![183533153720844, -43522840423212, -3019678836137]]]
  hmulB := by decide  
  f := ![![![-5547483947256198496458083, -123587870240717867810896, -206448641085505470072126]], ![![-21057761390721557947356852, -469128690963349346916163, -783660892893164543576940]], ![![-21590950351272383882249228, -481007172937674105523019, -803503426444244970188501]]]
  g := ![![![-137386059803, 44458438502, -8061165702], ![-5078519643468, -4205087284855, 5406095098668], ![6731894095976, 1322679124289, -3019678836137]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [44, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 46], [0, 1]]
 g := ![![[12, 7], [17, 36], [29, 36], [13, 27], [1]], ![[29, 40], [44, 11], [9, 11], [45, 20], [1]]]
 h' := ![![[36, 46], [4, 17], [40, 41], [39, 41], [3, 36], [0, 1]], ![[0, 1], [5, 30], [12, 6], [11, 6], [30, 11], [36, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [19, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [44, 11, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1688, 2334, -1581]
  a := ![1, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1516, 1227, -1581]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5547483947256198496458083, -123587870240717867810896, -206448641085505470072126]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-5547483947256198496458083, -123587870240717867810896, -206448641085505470072126]] 
 ![![47, 0, 0], ![34, 1, 0], ![2, 0, 1]] where
  M :=![![![-5547483947256198496458083, -123587870240717867810896, -206448641085505470072126], ![-21057761390721557947356852, -469128690963349346916163, -783660892893164543576940], ![-33663724155274780464068244, -749966653761869633836764, -1252789583856513890493103]]]
  hmulB := by decide  
  f := ![![![-6811836101629, 1807405810024, -8061165702]], ![![-4945205667170, 1128213268213, 109191818400]], ![![3615095351438, -849106995812, -64591514203]]]
  g := ![![![-19842533551080426611561, -123587870240717867810896, -206448641085505470072126], ![-75320513025135129043690, -469128690963349346916163, -783660892893164543576940], ![-120410186375706066651746, -749966653761869633836764, -1252789583856513890493103]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-6811836101629, 1807405810024, -8061165702]] ![![-5547483947256198496458083, -123587870240717867810896, -206448641085505470072126]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [18, 46, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 15, 50], [5, 37, 3], [0, 1]]
 g := ![![[43, 18, 1], [36, 25], [2, 32, 44], [26, 40], [1]], ![[49, 33, 10, 5], [31, 52], [6, 0, 11, 51], [23, 10], [28, 12, 21, 26]], ![[0, 50, 52, 27], [32, 6], [18, 3, 34, 35], [43, 10], [1, 2, 5, 27]]]
 h' := ![![[21, 15, 50], [12, 4, 52], [17, 34, 5], [15, 5, 16], [35, 7, 26], [0, 1]], ![[5, 37, 3], [21, 15, 4], [46, 46, 30], [48, 0, 47], [12, 3, 40], [21, 15, 50]], ![[0, 1], [0, 34, 50], [29, 26, 18], [22, 48, 43], [1, 43, 40], [5, 37, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 1], []]
 b := ![[], [22, 3, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [18, 46, 27, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-61692, 94340, -48548]
  a := ![0, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1164, 1780, -916]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![339425088305094559, 7561774701600036, 12631645065971429]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![339425088305094559, 7561774701600036, 12631645065971429]] 
 ![![59, 0, 0], ![15, 1, 0], ![48, 0, 1]] where
  M :=![![![339425088305094559, 7561774701600036, 12631645065971429], ![1288427796729085758, 28703832020180227, 47948614236742966], ![2059728816292289430, 45887018349084858, 76652446256923193]]]
  hmulB := by decide  
  f := ![![![1687695983, -533512866, 55612393]], ![![525218709, -120613247, -11103863]], ![![546839982, -200055690, 35026991]]]
  g := ![![![-6446110091280247, 7561774701600036, 12631645065971429], ![-24468867236225085, 28703832020180227, 47948614236742966], ![-39116845411462656, 45887018349084858, 76652446256923193]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-692665505624930911984203540606262160335475, -15431329850307309131448538579307786995240, -25777425175569849122935056685446487616676]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-692665505624930911984203540606262160335475, -15431329850307309131448538579307786995240, -25777425175569849122935056685446487616676]] 
 ![![59, 0, 0], ![44, 1, 0], ![38, 0, 1]] where
  M :=![![![-692665505624930911984203540606262160335475, -15431329850307309131448538579307786995240, -25777425175569849122935056685446487616676], ![-2629297367908124610539375781915541736900952, -58575971560947223902313641576238670540011, -97848839902061625640215729108816336219072], ![-4203293012639470141947126717004936010415432, -93641736752881865058066094434649889214408, -156424811463008849542529370685055006759083]]]
  hmulB := by decide  
  f := ![![![-2665367820095522380537, 729682244581267497112, -17211090467972393844]], ![![-2017486700202307947724, 493627709629327414365, 23683670715543599568]], ![![-484947787187690676730, 167894098232444777464, -25108148786788909963]]]
  g := ![![![16370426516275338245272276456444864354047, -15431329850307309131448538579307786995240, -25777425175569849122935056685446487616676], ![62140699950032118906620714467355602426852, -58575971560947223902313641576238670540011, -97848839902061625640215729108816336219072], ![99340444747146918698710127527995752065486, -93641736752881865058066094434649889214408, -156424811463008849542529370685055006759083]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8131101143837078329576356515, -31038556774549070205578707366, 20755566802916845733546516095]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-8131101143837078329576356515, -31038556774549070205578707366, 20755566802916845733546516095]] 
 ![![59, 0, 0], ![58, 1, 0], ![19, 0, 1]] where
  M :=![![![-8131101143837078329576356515, -31038556774549070205578707366, 20755566802916845733546516095], ![2117067813897518264821744641690, -475226147639292305729114035429, -51604536717813519149643089908], ![-1048864977106486896147283509642, 1118525565041680908137726266494, -526830684357105824878757125337]]]
  hmulB := by decide  
  f := ![![![308084710176205912185807727114617749918107817027102421507125, 6863567979000349527401242384869498825005688562002723088588, 11465318396560312162353442660294719925593010508450108592083]], ![![322684333333374487242998293627082897078995601007353415657724, 7188821075623361751715185071272981436088132421329746294011, 12008640808993555564803564182581215118823689765983299742216]], ![![130900947519577963116700418470923517983137556418663302373963, 2916235444798031716700945016287414653146538073594717613806, 4871455778720774148365252269550382843921019705521314269628]]]
  g := ![![![23690668178382863129772963812, -31038556774549070205578707366, 20755566802916845733546516095], ![519672382620592014592433515336, -475226147639292305729114035429, -51604536717813519149643089908], ![-947687538080321506702356298049, 1118525565041680908137726266494, -526830684357105824878757125337]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![339425088305094559, 7561774701600036, 12631645065971429]] ![![-692665505624930911984203540606262160335475, -15431329850307309131448538579307786995240, -25777425175569849122935056685446487616676]]
  ![![-308084710176205912185807727114617749918107817027102421507125, -6863567979000349527401242384869498825005688562002723088588, -11465318396560312162353442660294719925593010508450108592083]] where
 M := ![![![-308084710176205912185807727114617749918107817027102421507125, -6863567979000349527401242384869498825005688562002723088588, -11465318396560312162353442660294719925593010508450108592083]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-308084710176205912185807727114617749918107817027102421507125, -6863567979000349527401242384869498825005688562002723088588, -11465318396560312162353442660294719925593010508450108592083]] ![![-8131101143837078329576356515, -31038556774549070205578707366, 20755566802916845733546516095]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [46, 32, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 56, 40], [15, 4, 21], [0, 1]]
 g := ![![[13, 30, 5], [36, 45], [14, 54, 12], [57, 21, 58], [1]], ![[14, 26, 55, 44], [24, 25], [14, 54, 57, 40], [25, 23, 5, 50], [50, 11, 26, 11]], ![[34, 25, 4, 53], [51, 57], [35, 55, 3, 30], [36, 49, 48, 29], [7, 32, 54, 50]]]
 h' := ![![[12, 56, 40], [49, 32, 26], [27, 58, 44], [1, 58, 45], [15, 29, 27], [0, 1]], ![[15, 4, 21], [50, 49, 42], [42, 59, 56], [13, 60, 60], [38, 4, 48], [12, 56, 40]], ![[0, 1], [24, 41, 54], [33, 5, 22], [4, 4, 17], [3, 28, 47], [15, 4, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 22], []]
 b := ![[], [32, 52, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [46, 32, 34, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![587735, -9338673, 6209190]
  a := ![1, -1, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9635, -153093, 101790]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [32, 4, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 0, 54], [16, 66, 13], [0, 1]]
 g := ![![[55, 48, 59], [61, 52, 40], [12, 59], [], [65, 1], []], ![[18, 42, 45, 10], [26, 48, 22, 16], [52, 23], [14, 60], [3, 1], [64, 35]], ![[11, 56, 38, 46], [5, 43, 9, 3], [52, 16], [46, 60], [], [38, 35]]]
 h' := ![![[49, 0, 54], [58, 54, 40], [32, 53, 24], [9, 10, 40], [64, 43], [0, 0, 1], [0, 1]], ![[16, 66, 13], [7, 34, 62], [46, 7, 24], [13, 34, 31], [27, 0, 44], [18, 31, 66], [49, 0, 54]], ![[0, 1], [42, 46, 32], [17, 7, 19], [26, 23, 63], [15, 24, 23], [45, 36], [16, 66, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 7], []]
 b := ![[], [47, 32, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [32, 4, 2, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![335, -67, 0]
  a := ![-1, 1, 0]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, -1, 0]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-819997703469268518039634450858265577830229953500300744452036346703936583221, -18268060031822270702313004311712307241003318793679339091724358539579695552, -30516070561717587339031788254392443378809060925368632826235631817477630662]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-819997703469268518039634450858265577830229953500300744452036346703936583221, -18268060031822270702313004311712307241003318793679339091724358539579695552, -30516070561717587339031788254392443378809060925368632826235631817477630662]] 
 ![![71, 0, 0], ![0, 71, 0], ![70, 60, 1]] where
  M :=![![![-819997703469268518039634450858265577830229953500300744452036346703936583221, -18268060031822270702313004311712307241003318793679339091724358539579695552, -30516070561717587339031788254392443378809060925368632826235631817477630662], ![-3112639197295193908581242401948029224638524214387600548276034445382718327524, -69343949956224151200558528441134629497809172497774217530656824544893751781, -115836321218901986785002589443921808480628078231775282927644339253694347980], ![-4975981320541065520217168841742684563220862731342893135631919016419847273828, -110855829347182075247060085097968607034483445608331252670856767764684658668, -185180271175126137985561117885056437978437250729549500458301163798588099761]]]
  hmulB := by decide  
  f := ![![![-11888910293011346093369988314699776531, 2457710258752939058739956633714691336, 421809029179457247515541593637697522]], ![![43024520976304639246585242551045147244, -24470037252071259092482943195719208395, 8216748834617731671250953088419469052]], ![![28774063456853359880243326622868565366, -18979647897132536878755758280377438688, 7130679911298202537745255024683200427]]]
  g := ![![![18537003321844543601304094745763457164597243820781740188513491274922500889, 25530932023538492530135130858476539373063948404625896203977655640972931608, -30516070561717587339031788254392443378809060925368632826235631817477630662], ![70364835042647115019280829001781653084583679744178440234634778906702620156, 96913173565885845857740800537946110976617965090263982508845120150377001789, -115836321218901986785002589443921808480628078231775282927644339253694347980], ![112487854390391044208057879017060085848869645348247491499283978161708728302, 154929020298033608505445168845146727770024670396685053166580465635923962352, -185180271175126137985561117885056437978437250729549500458301163798588099761]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [45, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 70], [0, 1]]
 g := ![![[0, 30], [0, 37], [], [], [], [1]], ![[0, 41], [0, 34], [], [], [], [1]]]
 h' := ![![[0, 70], [0, 39], [0, 45], [20], [37], [26], [0, 1]], ![[0, 1], [0, 32], [0, 26], [20], [37], [26], [0, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [0, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [45, 0, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2187, 1550, -1122]
  a := ![0, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1137, 970, -1122]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11888910293011346093369988314699776531, -2457710258752939058739956633714691336, -421809029179457247515541593637697522]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![11888910293011346093369988314699776531, -2457710258752939058739956633714691336, -421809029179457247515541593637697522]] 
 ![![71, 0, 0], ![31, 1, 0], ![45, 0, 1]] where
  M :=![![![11888910293011346093369988314699776531, -2457710258752939058739956633714691336, -421809029179457247515541593637697522], ![-43024520976304639246585242551045147244, 24470037252071259092482943195719208395, -8216748834617731671250953088419469052], ![-293710967369104423238060819189943663516, 51392483684840306954479210523674036668, 16253288417453527421231990107299739343]]]
  hmulB := by decide  
  f := ![![![819997703469268518039634450858265577830229953500300744452036346703936583221, 18268060031822270702313004311712307241003318793679339091724358539579695552, 30516070561717587339031788254392443378809060925368632826235631817477630662]], ![![401867154997781943208590287021891016019375391167562304595621988636686653625, 8952870576657951309468474114143889492519888100025827174283266750307948083, 14955415614537284426689972187747712017235337562228209866773928529514097162]], ![![589801098262790828619728438455839937543397332941639811774275417156295683363, 13139697616608228969734440551056653984220180159491570588710604254165788148, 21949344316231233355521008300460794225702042146072365882238092895564527881]]]
  g := ![![![1507877952498986381021239657373966147, -2457710258752939058739956633714691336, -421809029179457247515541593637697522], ![-6082281383559376702919205530133302819, 24470037252071259092482943195719208395, -8216748834617731671250953088419469052], ![-36877125920909333419469801412004606629, 51392483684840306954479210523674036668, 16253288417453527421231990107299739343]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-819997703469268518039634450858265577830229953500300744452036346703936583221, -18268060031822270702313004311712307241003318793679339091724358539579695552, -30516070561717587339031788254392443378809060925368632826235631817477630662]] ![![11888910293011346093369988314699776531, -2457710258752939058739956633714691336, -421809029179457247515541593637697522]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [45, 43, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 28, 53], [13, 44, 20], [0, 1]]
 g := ![![[61, 3, 64], [64, 36], [64, 1], [60, 72, 12], [42, 1], []], ![[12, 43, 27, 47], [60, 41], [18, 24], [3, 43, 34, 33], [34, 38], [58, 35]], ![[72, 51, 32, 17], [6, 12], [1, 38], [13, 30, 34, 20], [50, 54], [18, 35]]]
 h' := ![![[29, 28, 53], [42, 72, 65], [41, 72, 67], [1, 11, 1], [8, 47, 42], [0, 0, 1], [0, 1]], ![[13, 44, 20], [3, 41, 33], [41, 42, 48], [11, 53, 43], [0, 23, 32], [56, 37, 44], [29, 28, 53]], ![[0, 1], [47, 33, 48], [5, 32, 31], [14, 9, 29], [50, 3, 72], [16, 36, 28], [13, 44, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 2], []]
 b := ![[], [17, 5, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [45, 43, 31, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![350327, -12994, -49640]
  a := ![2, -2, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4799, -178, -680]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1044236086230665288496865228294967389502991943852223216968577556035, -23263684068807710057966457931725606361755628135458969302450263138, -38861062605038199481482280372559378335326148544526546259510363109]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-1044236086230665288496865228294967389502991943852223216968577556035, -23263684068807710057966457931725606361755628135458969302450263138, -38861062605038199481482280372559378335326148544526546259510363109]] 
 ![![79, 0, 0], ![0, 79, 0], ![41, 22, 1]] where
  M :=![![![-1044236086230665288496865228294967389502991943852223216968577556035, -23263684068807710057966457931725606361755628135458969302450263138, -38861062605038199481482280372559378335326148544526546259510363109], ![-3963828385713896347111192598001056590203267151541707718470057037118, -88306899640940790883324041421816703093408750648127137437878578281, -147513177416499529136863934540295575755919181495430000426371515632], ![-6336724160732282773023771307037068439102341221358522587319983877194, -141170709239302549275486056344654257353735598550462569412380220650, -235820077057440320020187975962112278849327932143557137864250093913]]]
  hmulB := by decide  
  f := ![![![364319584319364175915485492558193, -54357752734878399275909151619264, -26034091023719613358216345434653]], ![![-2655477284419400562538067234334606, 1043495521623513295788586934609129, -215141440252074424544160145727098]], ![![-654219814727973144961814869113607, 272964633427815274420386870456324, -62938675141097501473594513670062]]]
  g := ![![![6950221273112669496758332493417305344878229702194495945206928246, 10527591053696616183982831775501021734372400504356013270971869940, -38861062605038199481482280372559378335326148544526546259510363109], ![26382428966614991740509224280393190073283788478112940493812343086, 39961810171165175318071930613477037513124218256345985720788541337, -147513177416499529136863934540295575755919181495430000426371515632], ![42175936691427472757011844397589050553419037930725570444484430041, 63884442861068158116058853352174884523183277324149297007609137284, -235820077057440320020187975962112278849327932143557137864250093913]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [60, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 78], [0, 1]]
 g := ![![[35, 38], [36, 5], [51, 9], [2, 8], [62], [1]], ![[25, 41], [43, 74], [32, 70], [29, 71], [62], [1]]]
 h' := ![![[33, 78], [52, 65], [21, 59], [38, 3], [38, 61], [19, 33], [0, 1]], ![[0, 1], [64, 14], [72, 20], [58, 76], [76, 18], [2, 46], [33, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [26, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [60, 46, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![827, 95, 51]
  a := ![13, -1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16, -13, 51]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-364319584319364175915485492558193, 54357752734878399275909151619264, 26034091023719613358216345434653]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-364319584319364175915485492558193, 54357752734878399275909151619264, 26034091023719613358216345434653]] 
 ![![79, 0, 0], ![11, 1, 0], ![16, 0, 1]] where
  M :=![![![-364319584319364175915485492558193, 54357752734878399275909151619264, 26034091023719613358216345434653], ![2655477284419400562538067234334606, -1043495521623513295788586934609129, 215141440252074424544160145727098], ![8199968063376997288680800699499534, -835972427210128542173925421038582, -828354081371438871244426788882031]]]
  hmulB := by decide  
  f := ![![![1044236086230665288496865228294967389502991943852223216968577556035, 23263684068807710057966457931725606361755628135458969302450263138, 38861062605038199481482280372559378335326148544526546259510363109]], ![![195575004231028031906034305180325289553622513087546368419296331057, 4357056005035767107860190869250612317376210887825010123605461681, 7278289443948350929533785046056313132208947031458506446594753289]], ![![291702551144594017581944493161475274318357118012583469098952212326, 6498603219496530508898093458889417204326906945795013648754233302, 10855659224532297616758284328140029521703117833620023772359694983]]]
  g := ![![![-17453168617500511160530983383855, 54357752734878399275909151619264, 26034091023719613358216345434653], ![135337531370188050930455204853183, -1043495521623513295788586934609129, 215141440252074424544160145727098], ![387966203349764977120314037380208, -835972427210128542173925421038582, -828354081371438871244426788882031]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-1044236086230665288496865228294967389502991943852223216968577556035, -23263684068807710057966457931725606361755628135458969302450263138, -38861062605038199481482280372559378335326148544526546259510363109]] ![![-364319584319364175915485492558193, 54357752734878399275909151619264, 26034091023719613358216345434653]]
  ![![79, 0, 0]] where
 M := ![![![-79, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)


lemma PB177I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB177I1 : PrimesBelowBoundCertificateInterval O 31 79 177 where
  m := 11
  g := ![2, 2, 1, 2, 1, 3, 1, 1, 2, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB177I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0, I79N1]
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
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![59, 59, 59]
    · exact ![226981]
    · exact ![300763]
    · exact ![5041, 71]
    · exact ![389017]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
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
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N1, I47N1, I59N0, I59N1, I59N2, I71N1, I79N1]
  Il := ![[I37N1], [I41N1], [], [I47N1], [], [I59N0, I59N1, I59N2], [], [], [I71N1], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
