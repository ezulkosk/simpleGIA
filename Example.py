import z3
from npGIAforZ3 import MAXIMIZE, MINIMIZE, call_GIA

def example():
    '''
    Tested with Python3 
    Make sure PYTHONPATH is setup for z3
    '''
    
    #create solver instance
    s = z3.Solver()
    
    #variables
    x,y = z3.Ints('x y')
    
    #constraints
    s.add(z3.And(0 < x, x < 5))
    s.add(z3.And(0 < y, y < 5))
    s.add(x - y == 0)
    
    #we want to maximize x while minimizing y 
    #4 total Pareto points: (x,y) = (1,1) or (2,2) or (3,3) or (4,4)
    objectives = [(MAXIMIZE, x), (MINIMIZE, y)]
    
    # call GIA
    #   solver -- the Z3 solver instance
    #   objectives -- list of tuples (var, MINIMIZE/MAXIMIZE)
    #   desired_number_of_models (-1 for all)
    #   magnifying_glass -- True if you want to generate multiple solutions with the same objective values
    
    #   returns the list of Pareto optimal solutions
    pareto_front = call_GIA(solver=s, objectives=objectives, desired_number_of_models=-1, magnifying_glass=False)
    
    #iterate through front
    for i in pareto_front:
        print(i)

        
if __name__ == '__main__':
    example()
    

        
