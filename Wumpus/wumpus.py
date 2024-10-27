"""
File: wumpus.py
Implementation of a grid-based wumpus world of arbitrary size.
"""
import random

class WumpusWorld:
    def __init__(self, n:int=4, pits:int=3, wumpae:int=1):
        """
        Build an nxn Wumpus world containng pits and wumpae.

        Items at each square can be:
            W - Wumpus!
            P - Pit
            B - Breeze
            S - Stench
        """
        self.__grid = [[set() for i in range(n)] for i in range(n)]
        self.n = n
        self.__wumpae = wumpae

        # place the pits
        for i in range(pits):
            x,y = self.__empty()
            self.__place(x,y, 'P')
        
        # place wumpae
        for i in range(wumpae):
            x,y = self.__empty()
            self.__place(x,y,'W')

        # place the player
        self.__px, self.__py = self.__empty()

        # place the hints
        for i in range(self.n):
            for j in range(self.n):
                hint = None
                if 'W' in self.__grid[i][j]:
                    #stink up the joint
                    hint = 'S'
                elif 'P' in self.__grid[i][j]:
                    #breeze
                    hint = 'B'
                else:
                    continue
                for x,y in self.__adjacent(j,i):
                    self.__place(x,y,hint)


    def __empty(self):
        """
        Return the x,y coordinate of a random empty square.
        """
        while True:
            x = random.randrange(self.n)
            y = random.randrange(self.n)
            if len(self.__grid[y][x]) == 0:
                return x,y


    def __place(self, x:int, y:int, thing:str):
        """
        Place the thing at position x,y
        """
        self.__grid[y][x].add(thing)


    def __adjacent(self, x:int, y:int):
        """
        Return a list of adjacent squares to x,y.
        They are specified as (x,y) tuples.
        """
        result = []
        if x > 0:
            result.append((x-1,y))
        if x < self.n - 1:
            result.append((x+1,y))
        if y > 0:
            result.append((x, y-1))
        if y < self.n - 1:
            result.append((x,y+1))
        return result


    def __str__(self):
        s = ""
        for y in range(self.n):
            for x in range(self.n):
                if 'W' in self.__grid[y][x]:
                    s += "W"
                elif 'P' in self.__grid[y][x]:
                    s += "P"
                elif x == self.__px and y == self.__py:
                    s += "@"
                else:
                    s += "."
            s += "\n"
        return s
    
    def __new_xy(self, x, y, direction):
        """
        Returns the x,y point updated for the given direction. (N,S,E,W)
        """
        if direction == 'N':
            y -= 1
        elif direction == 'S':
            y += 1
        elif direction == 'E':
            x += 1
        elif direction == 'W':
            x -= 1
        return x,y

    def __offgrid(self, x,y):
        """
        Returns True if x,y is not in the grid, false otherwise.
        """
        return x<0 or x>=self.n or y<0 or y>=self.n

    def __move(self, direction):
        """
        Attempt to move in N, S, E, W. Returns true if we bump, false otherwise.
        """
        # compute the move
        x,y = self.__new_xy(self.__px, self.__py, direction)
        
        # handle bump
        if self.__offgrid(x,y):
            return True
        
        self.__px, self.__py = x,y
        return False
    
    def __fire(self, direction):
        """
        Attempt to process the FN, FS, FE, FW instructions
        Returns True if we strike a wumpus, false otherwise.
        """
        # compute where the arrow goes
        x,y = self.__new_xy(self.__px, self.__py, direction[-1])

        if self.__offgrid(x,y):
            return False
        
        if 'W' in self.__grid[y][x]:
            # we shot the wumpus!
            self.__grid[y][x].remove('W')
            self.__wumpae -= 1
            return True
        return False
    
    def play(self, agent):
        """
        Play the game using the agent function to make each move.
        The agent program is a function which receives a single parameter,
           def agent(percept:list)
        The percept list is a list of the following strings:
          O - You bumped into a wall with your last move
          S - You smell a wumpus
          B - You feel a breeze
          Y - Woeful scream of a dying Wumpus
        The agent program should return one of the following strings,
        indicating its next move:
          N - Go north (up)
          S - Go south (down)
          E - Go east (right)
          W - Go west (left)
          FN - Fire the arrow north 
          FS - Fire the arrow south 
          FE - Fire the arrow east
          FW - Fire the arrow west
        Should the player succeed in killing all the Wumpae, the game will 
        end and return the victory status.
        Should the player fall in a pit or get eaten, a similar status will
        be returned. The statuses are:
          E - Eaten by a wumpus
          F - Fallen into a pit
          W - Victory!
        """
        bumped = False
        yell = False

        # Game loop
        while True:
            # build percept
            percept = []
            x,y = self.__px,self.__py
            if bumped:
                percept.append("O")
                bumped = False
            if yell:
                percept.append("Y")
                yell = False
            percept.extend(self.__grid[y][x])
            
            # attempt the move
            move = str(agent(percept)).upper()
            if move[0] == 'F':
                yell = self.__fire(move)
            else:
                bumped = self.__move(move)
            
            # check for game over state
            if 'W' in self.__grid[self.__py][self.__px]:
                return 'E'
            elif 'P' in self.__grid[self.__py][self.__px]:
                return 'F'
            elif self.__wumpae == 0:
                return 'W'


def human(percept):
    """
    User interface for a human player.
    """
    msg = {'O':'Ouch! You bump into a wall.',
           'S':'You smell a terrible stench!',
           'B':'You feel a breeze.',
           'Y':'You hear a woeful scream!'}  
    
    for p in percept:
        print(msg[p])
    
    return input("\n? ").strip()


def run(agent=human):
    """
    Play the game
    """
    print("Welcome to Hunt the Wumpus!")
    print()
    n=int(input("How big of a grid would you like to play on? "))
    p=int(input("How many pits shall I place? "))
    nw=int(input("How many wumpae would you like to hunt? "))
    print()
    w = WumpusWorld(n,p,nw)

    print("You have entered a dark cave.")
    print("Possible moves:  N,  S,  E,  W")
    print("Fire an Arrow:  FN, FS, FE, FW")
    print()
    print("Good luck!")
    print()

    outcome = w.play(agent)
    if outcome == 'E':
        print("You have been eaten by a wumpus!")
        print("Game over!")
    elif outcome == 'F':
        print("You have fallen into a bottomless pit!")
        print("Game over!")
    elif outcome == 'W':
        print("You hear a mighty roar as the last wumpus falls!")
        print("Congratulations, you win!")

if __name__ == '__main__':
    run()
