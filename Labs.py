#!/usr/bin/python3
# Clés openssl utilisées fournies par Matéo Delerue-Houard
import math
import random 
import hashlib

class Groupe:
    def __init__(self,p,e,ordreN,l,A=None,B=None):
        """Constructeur de la classe où p est un nombre premier, e l'element neutre, ordreN l'orde de p et l le type du groupe.
        A et B permet de definir une courbe elliptique"""
        self.p = p
        self.e = e
        self.ordre = ordreN 
        self.l = l
        self.A = A
        self.B = B 


    def loi (self,g1,g2):
        " Méthode qui calcule et retourne g1 * g2."
        if self.l == "Zp-additif" :
            return (g1 + g2) % self.p
        if self.l == "Zp-multiplicatif":
            return (g1 * g2) % self.p
        if self.l == "courbe-P-256" or self.l == "courbe-P-384":
            G = Groupe(self.p, 1, self.p-1, "Zp-multiplicatif")
            if g1 == self.e :
                return g2
            if g2 == self.e :
                return g1
            x1, y1 = g1
            x2, y2 = g2
            if x1 == x2 and y1 != y2:
                return self.e
            if g1 == g2:
                inv = (G.squareAndMultiply(2 * y1, -1)) % self.p
                lam = (3 * (x1 ** 2) + self.A) * inv
                x = lam**2 - 2 * x1
            else:
                inv = (G.squareAndMultiply(x2 - x1, -1)) % self.p
                lam = (y2 - y1) * inv
                x = (lam ** 2) - x1 - x2
            return (x % self.p, (lam * (x1 - x) - y1) % self.p)

        if self.l == "Curve25519":
            if g1 == self.e :
                return g2
            if g2 == self.e :
                return g1

            x1,y1 = g1[0],g1[1]
            x2,y2 = g2[0],g2[1]
            G = Groupe(self.p,1,self.p-1,"Zp-multiplicatif")

            if x1 != x2:
                inv = G.squareAndMultiply(x2-x1,-1) % self.p
                lam = G.loi((y2-y1),inv)
                x3 = self.B*lam**2 - x1 - x2 - self.A
                return (x3 % self.p,(lam*(x1-x3)-y1)%self.p)
            elif y1!=0 :
                inv = G.squareAndMultiply(2*self.B*y1,-1) % self.p
                lam = G.loi((3*(x1**2) + 2*self.A*x1 + 1),inv)
                x3 = (self.B*lam**2 - self.A - 2 * x1)
                return (x3%self.p,(lam*(x1-x3)-y1)%self.p)
            return self.e
            

        else :
            raise ValueError("Valeur de l n'est pas correcte. Les valeurs valides sont 'Zp-additif', 'Zp-multiplicatif' ou 'courbe-P-256'.")
        
    
    def squareAndMultiply(self,g,k):
        "Méthode pour le calcul de g**k avec l'algorithme Square and Multiply"
        if k == 0 :
            return self.e
        if k == -1 :
            k = self.ordre-1
        h = self.e
        t = int(math.log(k)/math.log(2))
        x = self.e
        for i in range(t,-1,-1):
            h = self.loi(h,h)
            if k>>i&1 == 1:
                h = self.loi(h,g)
            else :
                x = self.loi(h,g)
        return h
    
    def MontgomeryLadder(self,g,k):
        " Méthode pour le calcul de g**k avec l'algorithme MontgomeryLadder"
        if k == 0 :
            return self.e
        if k == -1 :
            k = self.ordre-1
        h0 = self.e
        h1 = g
        t = int(math.log(k,2))
        for i in range(t,-1,-1):
            if k>>i&1 == 0 :
                h1 = self.loi(h0,h1)
                h0 = self.loi(h0,h0)
            else:
                h0 = self.loi(h0,h1)
                h1 = self.loi(h1,h1)
        return h0
    def reverse_bytes_25519(self,b):
        "Utiliser pour calculer DiffieHellmann quand on a une courbe curve25519."
        l = [(b>>8*(31-i)&0xff)<<(8*i) for i in range(32)]
        return sum(l)
    
    def s(self,x):
        "Utiliser pour calculer DiffieHellmann quand on a une courbe curve25519. On fais le calcul un point où la coordonnée x est s(x)*self.g."
        return self.reverse_bytes_25519(x) & ((1 << 255) - 8) | (1 << 254)

class Crypto(Groupe):
    def __init__(self,p,e,ordreN,l,g,A=None,B=None):
        "Constructeur où on a un objet Groupe constitué de (p,e,ordreN,l) et g son génerateur "
        super().__init__(p,e,ordreN,l,A,B)
        self.g = g

    def testDiffieHellman(self):
        " Méthode qui genère deux nombres a et b. Il compare (g**a)**b et (g**b)**a."
        a = random.randint(0,self.p - 1)
        b = random.randint(0,self.p - 1)

        ga = self.squareAndMultiply(self.g,a)
        gab = self.squareAndMultiply(ga,b)

        gb = self.MontgomeryLadder(self.g,b)
        gba = self.MontgomeryLadder(gb,a)
        

        if gab == gba :
            return True
        return False
    

    def DiffieHellman(self,a,b,A,B,K):
        " Méthode qui vérifie si (a,b,A,B,K) definit un protocole DiffieHellman"
        if self.l == "Curve25519":
            curve = Groupe(self.p,self.e,self.ordre,self.l,self.A,self.B)
            sa = self.s(a)
            sb = self.s(b)

            pointga = curve.squareAndMultiply(self.g,sa)
            pointgb = curve.squareAndMultiply(self.g,sb)

            ga = self.reverse_bytes_25519(pointga[0])
            gb = self.reverse_bytes_25519(pointgb[0])

            gab = self.reverse_bytes_25519(curve.squareAndMultiply(pointga,sb)[0])
            gba = self.reverse_bytes_25519(curve.squareAndMultiply(pointgb,sa)[0])

            
            if gab ==gba and gab == K and ga == A and gb == B :
                return True
            return False
        
        
        ga = self.squareAndMultiply(self.g,a)
        gb = self.squareAndMultiply(self.g,b)
        gab = self.squareAndMultiply(ga,b)
        gba = self.squareAndMultiply(gb,a)


        if self.l == "courbe-P-256":
            if A == ga and B == gb and K == gab[0] and K == gba[0] :
                return True
        if A == ga and B == gb and K == gab and K == gba :
            return True
        

        return False
    
    def ecdsa_sign(self,m,d):
        """Signe m un entier avec la cle privee d"""
        hm = int.from_bytes(hashlib.sha256(m).digest(),byteorder='big')
        N = self.ordre
        k = random.randint(1,N - 1) 
        K = self.squareAndMultiply(self.g,k)
        t = K[0] % N

        G = Groupe(N, 1, N-1, "Zp-multiplicatif")
        invk = G.squareAndMultiply(k,-1)
        s = G.loi((hm + d * t),(invk)) % N
        return (t,s)

    def ecdsa_verif(self,m,Q,signVerif):
        """Verifie si (t,s) est un signature valide du message m"""
        
        t,s = signVerif
        N = self.ordre  
        
        if t >= N or t < 1 or s >= N or s < 1:
            return False
        if self.l == 'courbe-P-384':
            hm = int.from_bytes(m,byteorder='big')
        if self.l == 'courbe-P-256':
            hm = int.from_bytes(hashlib.sha256(m).digest(),byteorder='big')

        G = Groupe(N, 1, N-1, "Zp-multiplicatif")
        invs = G.squareAndMultiply(s,-1)
        R = self.loi(self.squareAndMultiply(self.g,hm*invs), self.squareAndMultiply(Q,t*invs))
        return R[0] % N == t

def test_lab1():
    print("Test Lab 1 : \n-Class Groupe")
    p = 23
    e = 0
    ordreN = p

    l = "Zp-additif"
    G1 = Groupe(p,e,ordreN,l)
    testloi = G1.loi(2,23)
    print("calcul de loi: ",testloi)

    sq = G1.squareAndMultiply(5,7)
    ml = G1.MontgomeryLadder(5,7)
    print("Calcul de puissance: ")
    print("  squareAndMultiply==montgomeryladder: ",sq==ml)
    
    sq1 = G1.squareAndMultiply(5,-1)
    ml1 = G1.MontgomeryLadder(5,-1)
    print("Calcul de l'inverse:")
    print("  squareAndMultiply==montgomeryladder ",sq1==ml1)


    print("-Class Crypto")
    C = Crypto(p,e,ordreN,l,5)

    bool1 = C.testDiffieHellman()
    print("testDiffieHellman: ",bool1)

    a,b = 5,6
    A,B,K = 2,7,12
    bool2 = C.DiffieHellman(a,b,A,B,K)
    print("DiffieHellman: ",bool2)

    print("Lab1 OK")

def test_lab2():
    print("Test Lab 2 :")
    
    f = open("keys/dh/dh_param.der",'rb')
    dh_param = f.read()
    f.close()
    p = int.from_bytes(dh_param[8:265], byteorder='big')
    e = 1
    g = int.from_bytes(dh_param[268:525], byteorder='big')
    N = int.from_bytes(dh_param[527:560], byteorder='big')

    l = "Zp-multiplicatif"
    C2 = Crypto(p,e,N,l,g)
    assert C2.testDiffieHellman()
    print("test DiffieHellman : passed")

    f = open("keys/DH/keys/alice.key", "r")
    alice_priv = f.read()
    f.close()
    a = int(alice_priv, 16)
    

    f = open("keys/DH/keys/alice.pub", "r")
    alice_pub = f.read()
    f.close()
    ga = int(alice_pub, 16)

    f = open("keys/DH/keys/bob.key", "r")
    bob_priv = f.read()
    f.close()
    b = int(bob_priv, 16)

    f = open("keys/DH/keys/bob.pub", "r")
    bob_pub = f.read()
    f.close()
    gb = int(bob_pub, 16)


    K = C2.squareAndMultiply(gb, a)
    
    assert C2.DiffieHellman(a,b,ga,gb,K)    
    print("DiffieHellman: passed")

    print("Lab2 OK")

def test_lab3():

    print("Test Lab 3 :")

    p = 2**256 - 2**224 + 2**192 + 2**96 - 1
    A = -3
    B = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b 
    N = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
    Gx = 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
    Gy = 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
    G = (Gx,Gy)
    e = (0,0)

    print("class Groupe")
    groupeElliptique = Groupe(p,e,N,"courbe-P-256",A,B)
    assert groupeElliptique.squareAndMultiply(G,N)
    print("test Square sur N*G : passed")

    print("class Crypto")
    CElliptique = Crypto(p,e,N,"courbe-P-256",G,A,B)
    assert CElliptique.testDiffieHellman()
    print("test DiffieHellman: passed")

    f = open("keys/EC/keys/alice.key", "r")
    alice = f.read()
    f.close()
    a = int(alice,16)

    f = open("keys/EC/keys/alice.pub", "r")
    a_x = int(f.read(64), 16)
    a_y = int(f.read(64), 16)
    f.close()
    ga = (a_x, a_y)

    f = open("keys/EC/keys/bob.key", "r")
    bob = f.read()
    f.close()
    b = int(bob,16)

    f = open("keys/EC/keys/bob.pub", "r")
    b_x = int(f.read(64), 16)
    b_y = int(f.read(64), 16)
    f.close()
    gb = (b_x, b_y)

    assert CElliptique.squareAndMultiply(G, a) == ga
    print("Clé publique Alice = clé privé Alice * G: passed \n C'est un point de la courbe")


    K = CElliptique.squareAndMultiply(gb, a)[0]
    assert CElliptique.DiffieHellman(a, b, ga, gb, K)
    print("DiffieHellman: passed")

    f = open("Labs.pdf", "rb")
    labs = f.read()
    f.close()

    s = CElliptique.ecdsa_sign(labs, a)
    assert CElliptique.ecdsa_verif(labs, ga, s)
    print("Signature ECDSA: passed")

    print("Lab3 OK")

def test_lab4():
    print("Test Lab 4 :")
    p =  2**255 - 19
    A = 486662
    B = 1 
    N = 2**252 + 0x14def9dea2f79cd65812631a5cf5d3ed
    Gx = 9
    Gy = 0x20ae19a1b8a086b4e01edd2c7748d14c923d4d7e6d7c61b229e9c5a27eced3d9
    G = [Gx,Gy]
    e = [0,1]
    l = "Curve25519"
    
    C = Crypto(p,e,N,l,G,A,B)
    assert C.testDiffieHellman()
    print("testDiffieHelman: passed")

    invG = C.squareAndMultiply(G,-1)
    assert (invG[0],-invG[1]%p) == (G[0],G[1])
    print("Inverse de G : passed")

    f = open("keys/X25519/keys/alice.key", "r")
    a = int(f.read(), 16)
    f.close()

    f = open("keys/X25519/keys/alice.pub", "r")
    ga = int(f.read(), 16)
    f.close()

    s = C.reverse_bytes_25519(a) & ((1 << 255) - 8) | (1 >> 254)
    A = C.squareAndMultiply(G, s)
    assert ga == C.reverse_bytes_25519(A[0])
    print("Clé publique Alice appartient à la courbe: passed")

    f = open("keys/X25519/keys/bob.key", "r")
    b = int(f.read(), 16)
    f.close()

    f = open("keys/X25519/keys/bob.pub", "r")
    gb = int(f.read(), 16)
    f.close()
    
    t = C.s(b)
    B = C.squareAndMultiply(G, t)
    assert gb == C.reverse_bytes_25519(B[0])
    print("Clé publique Bob appartient à la courbe: passed")

    K = C.reverse_bytes_25519(C.squareAndMultiply(B, s)[0])
    assert C.DiffieHellman(a,b,ga,gb, K)
    print("DiffieHellman: passed")

    print("Lab4 OK")

def test_lab5():
    print("Test Lab 5 :")
    #On a fait avec la courbe P-384 car aucune P-383
    # Valeur de la courbe pris sur https://neuromancer.sk/std/nist/P-384#
    #La courbe P-384 est un courbe elliptique
    
    p = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff
    N = 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973
    A = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffc
    B = 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef
    Gx = 0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7
    Gy = 0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f
    G = (Gx,Gy)
    l = 'courbe-P-384'
    e = (0,0)

    GMultiplicatif = Groupe(p,1,p-1,"Zp-multiplicatif")
    CP384 = Crypto(p,e,N,l,G,A,B)
    assert e == CP384.squareAndMultiply(G,N)
    print("N*G = e : passed")
    assert CP384.testDiffieHellman()
    print("testDiffieHellman: passed")
    
    #On extrait tous les données nécéssaires pour verifie la validité de la signature de wikipédia
    f = open("wiki/wikipedia-org.der", 'rb')
    message = f.read()[4:2009]
    f.close()
    h = hashlib.sha384(message).digest()

    #On a pris la signature de wikipedia-org.pem
    f = open("wiki/signWiki.txt",'rb')
    t=f.read(6)#Seq||tailleSig||02
    tailleR = int(f.read(2),16)
    r =int(f.read(tailleR*2),16)
    f.read(2) #02
    tailleS = int(f.read(2),16)
    s = int(f.read(tailleS*2),16)
    f.close()

    #On copier coller la publiqueKey prise dans le wikipedia-org-authority.pem
    f = open("wiki/publicKey.txt", "r")
    f.read(2) #04
    Q_x = int(f.read(96), 16)
    Q_y = int(f.read(96), 16)
    f.close()
    Q = (Q_x,Q_y)

    # On verifie que Q est un point de la courbe P-384
    # y**2 = x**3 -3x + b
    y2 = GMultiplicatif.squareAndMultiply(Q_x,3)+ A*Q_x + B
    assert  GMultiplicatif.squareAndMultiply(Q_y,2) % p == y2 % p
    print("Q est un point de la courbe: passed")
    
    #On verifie que la signature est valide
    sign_verif = CP384.ecdsa_verif(h,Q,(r,s))
    assert sign_verif==True
    print("sign_verif est bien une signature : passed")

    print("Lab5 OK")

if __name__ == "__main__":
    
    test_lab1()
    
    print("---------------------------")
    
    test_lab2()

    print("---------------------------")

    test_lab3()

    print("---------------------------")

    test_lab4()

    print('---------------------------')
    
    test_lab5()
    
    
