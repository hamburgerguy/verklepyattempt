#import library for generating fields and polynomial proofs
import polycule

''' Verkle Tree implementation '''

class VerkleTree:
    ### initializes verkle tree parameters ###
    def __init__(self, datablocks: list,  depth: int):
        # the number of children of parent node is 2 ** exponent. exponent is not checked
        datalength = len(datablocks)
        # check datalength
        if datalength == 0:
            raise ValueError('length not a power of 2')
        exp2 = 0   # datalength should be equal to 2 ** exponent2
        while datalength > 1:
            if datalength & 1 != 0:
                raise ValueError('length not a power of 2')
            exp2 += 1
            datalength >>= 1
        if exp2 % depth != 0:
            raise ValueError('length not a power of 2 ** exponent')

        self.exp1 = exp2 // depth  # tree depth minus the level of datablocks
        self.exponent = depth
        self.datablocks = datablocks
        self.verkletreecommits = []
        self.verkletreeblipoly = []

    def hashAllCurrNodes(self, nodes: list) -> list:
        return [polycule.hash_to_scalar('verkle', node) for node in nodes]

    ### returns total depth of the tree
    def depth(self) -> str:
        totaldepth = self.exponent
        return "Total depth of the verkle tree is: " + str(totaldepth)

    ### builds verkle-tree and returns the root ###
    def root(self, printAllCommit=False) -> polycule.Point:
        veclen = 2 ** self.exponent   # vector/polynomial length
        currnodes = self.datablocks
        self.G_vec = polycule.PointVector([polycule.random_point() for i in range(veclen)])   # (public)
        while len(currnodes) > 1:
            cache1 = []   # for commitments (public)
            cache2 = []   # for blinding factors and polynomial (private)
            nodehashes = self.hashAllCurrNodes(currnodes)
            for i in range(0, len(nodehashes), veclen):
                coords = [(polycule.Scalar(j + 1), hash) for j, hash in enumerate(nodehashes[i:i + veclen])]
                poly = polycule.lagrange(coords)   # polynomial coefficients
                r = polycule.random_scalar()   # blinding factor
                P = poly ** self.G_vec + r * polycule.H   # the actual commitment
                cache1.append(P)
                cache2.append((poly, r))
            self.verkletreecommits.append(cache1)
            self.verkletreeblipoly.append(cache2)
            currnodes = cache1

        if printAllCommit == True:
            print('1st node.\n')
            for i in range(self.exp1):
                print(f'Level {i + 2} commitments of tree is: {self.verkletreecommits[i]}\n')

        return currnodes[0]   # return verkle tree root commitment

    ### insert an element to the tree at the given position ###
    def insert(self, position: int, element: str):
        newlist = self.datablocks
        newlist.insert(position, element)
        if len(newlist) > 2**self.exponent**self.exp1:
            newlist.pop()

        newTree = VerkleTree(newlist, self.exponent)
        return



    ### open verkle tree at given index ###
    def open(self, index: int) -> tuple:

        print('opening data at given index position')
        num_blocks = len(self.datablocks)
        if not(0 <= index < num_blocks):
            raise ValueError(f'index must be in range({num_blocks})')

        datum = self.datablocks[index]
        currpathdata = datum
        proofs = []
        for i in range(self.exp1):
            # initialize prove
            curridx = index & ((1 << self.exponent) - 1)
            x = polycule.Scalar(curridx + 1)
            v = polycule.hash_to_scalar('verkle', currpathdata)
            index >>= self.exponent   # move one level up the tree
            curridx = index & ((1 << self.exponent) - 1)
            P = self.verkletreecommits[i][curridx]
            poly, r = self.verkletreeblipoly[i][curridx]
            transcript = polycule.prove(self.G_vec, P, x, v, poly, r)
            proofs.append(transcript)
            currpathdata = P
        return datum, proofs



### check function verifies verkle tree ###
def check(index: int, datum: object, proofs: list, root: polycule.Point) -> bool:
    # first check: the v of the first proof should be the hash_to_scalar of datum
    # second check: the P of last proof should be the root
    if proofs[0]['state'][2] != polycule.hash_to_scalar('verkle', datum) or proofs[-1]['state'][0] != root:
        return False
    for proof in proofs:
        #  verify the proofs
        if not polycule.verify(proof):
            return False
    return True

if __name__ == '__main__':
    # len(data) should be a power of 2 exponent

    data = ['cg8sdak', 'un10yw5', '2i7evx2', '9belwa1', '4jcjdrs', 'bavy0qm', 'wr2m1n0', 'mhkncvp',
            'o4r4oc1', 'r4wucd8', 'kk1trrs', 'zpw91dg', 'mncp76e', '0iexfpy', 'q9hkpa9', '7g1xqad']

    verkle = VerkleTree(data, 2)   # where exponent = 2 in this example
    root = verkle.root(printAllCommit=True)# root commitment is a Point
    print(f'return total depth of verkle tree: {verkle.depth()}')
    datum, proofs = verkle.open(11)   # open verkle tree for data at index 11
    print(f'index 11: {verkle.open(11)[0]} proofs: {proofs}')

    # verify provided proofs
    if check(11, datum, proofs, root):
        print('\nverkle tree proofs pass')
    else:
        print('\nverkle tree proofs dont pass :(')
    verkle.insert(11,'66xj7yj') # insert data into verkle tree
    newdatum = verkle.open(11)[0]
    print(f'new index at 11: {newdatum}')

