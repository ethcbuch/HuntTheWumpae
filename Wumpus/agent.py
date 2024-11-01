from logic import expr, FolKB
from collections import deque

class WumpusKnowledge:
    def __init__(self):
        self.kb = FolKB()
        self.last_move = None
        self.moves_taken = 0
        self.current_position = 'Here'
        self.wumpus_kills = 0
        self.blocked_directions = set()
        self.visited_positions = {'Here'}
        self.move_sequence = ['North', 'East', 'South', 'West']
        self.current_move_index = 0
        self.safe_squares = {'Here'}
        self.last_safe_position = 'Here'
        self.move_history = deque(maxlen=20)
        self.safe_history = deque(maxlen=20)
        self.shots_fired = set()
        self.last_stench_location = None
        self.breeze_squares = set()
        self.confirmed_no_pit = {'Here'}
        self.last_bump_direction = None
        
        #Basic facts
        self.kb.tell(expr('Location(Here)'))
        self.kb.tell(expr('AgentAt(Here)'))
        self.kb.tell(expr('SafeSquare(Here)'))
        self.kb.tell(expr('VisitedSquare(Here)'))
        self.kb.tell(expr('KnownSafe(Here)'))
        
        #Direction and wall rules
        for direction in self.move_sequence:
            self.kb.tell(expr(f'Location({direction})'))
            self.kb.tell(expr(f'Direction({direction})'))
            self.kb.tell(expr(f'AdjacentSquares(Here, {direction})'))
            self.kb.tell(expr(f'MovementOption({direction})'))
        
        #Movement rules
        self.kb.tell(expr('Location(x) & Direction(d) & MovementOption(d) ==> PossibleMove(d)'))
        self.kb.tell(expr('Location(x) & Direction(d) & WallFound(d) ==> BlockedDirection(d)'))
        self.kb.tell(expr('Location(x) & Direction(d) & BlockedDirection(d) & Direction(alt) & NotOpposite(d, alt) ==> TryAlternative(alt)'))
        
        #Opposite direction
        self.kb.tell(expr('Direction(North) & Direction(South) ==> OppositeDirection(North, South)'))
        self.kb.tell(expr('Direction(South) & Direction(North) ==> OppositeDirection(South, North)'))
        self.kb.tell(expr('Direction(East) & Direction(West) ==> OppositeDirection(East, West)'))
        self.kb.tell(expr('Direction(West) & Direction(East) ==> OppositeDirection(West, East)'))
        
        #Alternative direction
        self.kb.tell(expr('Direction(d1) & Direction(d2) & NotOpposite(d1, d2) ==> AlternativeDirection(d1, d2)'))
        
        #Safety rules
        self.kb.tell(expr('Location(x) & SafeSquare(x) & BreezePresent(x) ==> SafeButDangerous(x)'))
        self.kb.tell(expr('Location(x) & SafeSquare(x) & NoBreeze(x) ==> FullySafe(x)'))
        self.kb.tell(expr('Location(x) & FullySafe(x) ==> PreferredSquare(x)'))
        
        #Backtracking rules
        self.kb.tell(expr('Location(x) & Direction(back) & OppositeDirection(last, back) & WallFound(last) ==> BacktrackOption(back)'))
        self.kb.tell(expr('Location(x) & Direction(d) & SafeSquare(x) & LastVisited(x) ==> ReturnMove(d)'))

    def get_opposite_direction(self, direction):
        opposites = {'North': 'South', 'South': 'North', 'East': 'West', 'West': 'East'}
        return opposites.get(direction)

    def get_alternative_directions(self, blocked_dir):
        alternatives = []
        for d in self.move_sequence:
            if d != blocked_dir and d != self.get_opposite_direction(blocked_dir):
                alternatives.append(d)
        return alternatives

    def update_knowledge(self, percepts):
        print(f"\nMove {self.moves_taken} - Processing percepts: {percepts}")
        
        if 'O' in percepts and self.last_move:
            print(f"Bump! Wall detected at {self.last_move}")
            self.kb.tell(expr(f'WallFound({self.last_move})'))
            self.kb.tell(expr(f'BlockedDirection({self.last_move})'))
            self.blocked_directions.add(self.last_move)
            self.last_bump_direction = self.last_move
            
            for alt_dir in self.get_alternative_directions(self.last_move):
                self.kb.tell(expr(f'NotOpposite({self.last_move}, {alt_dir})'))
                self.kb.tell(expr(f'AlternativeDirection({self.last_move}, {alt_dir})'))
            return
            
        if self.last_move and 'O' not in percepts:
            self.current_position = self.last_move
            self.kb.tell(expr(f'AgentAt({self.last_move})'))
            self.kb.tell(expr(f'VisitedSquare({self.last_move})'))
            self.kb.tell(expr(f'LastVisited({self.last_move})'))
            self.visited_positions.add(self.last_move)
            self.move_history.append(self.last_move)
            self.last_bump_direction = None
        
        if not any(p in percepts for p in ['B', 'S']):
            self.kb.tell(expr('NoBreeze(Here)'))
            self.kb.tell(expr('SafeSquare(Here)'))
            self.kb.tell(expr('FullySafe(Here)'))
            self.safe_squares.add(self.current_position)
            self.safe_history.append(self.current_position)
            self.last_safe_position = self.current_position
            
        if 'B' in percepts:
            print("Breeze detected!")
            self.kb.tell(expr('BreezePresent(Here)'))
            self.breeze_squares.add(self.current_position)
            
        if 'S' in percepts:
            if self.current_position != self.last_stench_location:
                self.last_stench_location = self.current_position
                self.shots_fired.clear()
            self.kb.tell(expr('StenchPresent(Here)'))
            
        if 'Y' in percepts:
            self.kb.tell(expr('WumpusKilled'))
            self.wumpus_kills += 1

def agent(percept):
    if not hasattr(agent, 'kb_agent'):
        agent.kb_agent = WumpusKnowledge()

    agent.kb_agent.update_knowledge(percept)
    print("\nAnalyzing possible moves...")

    #Shoot all directions when stench
    if 'S' in percept:
        unshot_directions = [d for d in agent.kb_agent.move_sequence 
                           if d not in agent.kb_agent.blocked_directions 
                           and d not in agent.kb_agent.shots_fired]
        
        if unshot_directions:
            shoot_dir = unshot_directions[0]
            agent.kb_agent.shots_fired.add(shoot_dir)
            print(f"Shooting arrow {shoot_dir}")
            return f'F{shoot_dir[0]}'

    #Try alternate directions on bump
    if agent.kb_agent.last_bump_direction:
        alternatives = agent.kb_agent.get_alternative_directions(agent.kb_agent.last_bump_direction)
        for alt_dir in alternatives:
            if alt_dir not in agent.kb_agent.blocked_directions:
                print(f"Trying alternative direction after bump: {alt_dir}")
                agent.kb_agent.last_move = alt_dir
                return alt_dir[0]

    #Backtrack to safe square if breeze
    if 'B' in percept:
        if agent.kb_agent.last_safe_position != agent.kb_agent.current_position:
            opp_dir = agent.kb_agent.get_opposite_direction(agent.kb_agent.last_move)
            if opp_dir and opp_dir not in agent.kb_agent.blocked_directions:
                print(f"Retreating from breeze: {opp_dir}")
                agent.kb_agent.last_move = opp_dir
                return opp_dir[0]

    #Try safe moves
    for direction in agent.kb_agent.move_sequence:
        if (direction not in agent.kb_agent.blocked_directions and
            direction not in agent.kb_agent.visited_positions and
            bool(agent.kb_agent.kb.ask(expr(f'PossibleMove({direction})')))):
            agent.kb_agent.last_move = direction
            print(f"Taking safe unexplored move: {direction}")
            return direction[0]

    #Try unblocked directions
    for direction in agent.kb_agent.move_sequence:
        if direction not in agent.kb_agent.blocked_directions:
            agent.kb_agent.last_move = direction
            print(f"Taking available move: {direction}")
            return direction[0]

    #Reset if stuck
    agent.kb_agent.blocked_directions.clear()
    agent.kb_agent.move_sequence = ['East', 'South', 'West', 'North']
    agent.kb_agent.current_move_index = 0
    new_dir = agent.kb_agent.move_sequence[0]
    agent.kb_agent.last_move = new_dir
    return new_dir[0]
