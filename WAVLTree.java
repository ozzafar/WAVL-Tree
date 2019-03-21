
/**
 *
 * WAVLTree
 *
 * An implementation of a WAVL Tree. (Haupler, Sen & Tarajan ‘15)
 * Oz Zafar , 206039984 , ozzafar
 * Kobi Somech , 204427918 , kobisomech 
 */


public class WAVLTree {
	
	
	public enum Direction {
		Right, Left;
		// return the opposite direction
		public static Direction flip_direction(Direction direction) {
			if (direction == Right)
				return Left;
			else
				return Right;

		}
    }
	
	
	public enum Action {
		Insert, Delete;
	}

	public enum Case {
		HasRightSonCase, SpecialCase;
	}

	private final WAVLExtNode ext = new WAVLExtNode();
	private WAVLNode root, pointer, min, max;
	
	public WAVLTree() {
	}

	/**
	 * public boolean empty()
	 *
	 * returns true if and only if the tree is empty
	 *
	 */

	
	public boolean empty() {
		return root == null;
	}
	
	
	/**
	 *
	 * return Right if son is father's right son and the same for Left
	 *
	 */

	private Direction WhichDirection(WAVLNode father ,WAVLNode son) {   
		if (father.getRight().getKey() == son.getKey())
			return Direction.Right;
		else
			return Direction.Left;
	}

	/**
	 * public String search(int k)
	 *
	 * returns the info of an item with key k if it exists in the tree otherwise,
	 * returns null
	 */
	public String search(int k) {
		if (empty()) {
			return null;
		}
		WAVLNode curr = root;
		int key;
		while (curr.isInnerNode()) {
			pointer = curr;
			key = curr.getKey();
			if (key == k) {
				return curr.getValue();
			}
			if (key > k) {
				curr = curr.getLeft();
			}
			if (key < k) {
				curr = curr.getRight();
			}
		}
		return null;
	}

	
	//after inserting a node - increase all it's parents' subtreesize
	//after deleting a node - decrease all it's parents' subtreesize 
	
	public void subTreeSizeUpdates(WAVLNode node, Action action) {
		while (node != null) {
			if (action == Action.Insert)
				node.subtreeSize += 1;
			else
				node.subtreeSize -= 1;

			node = node.getFather();
		}
	}
	
	
	/**
	 * public int insert(int k, String i)
	 *
	 * inserts an item with key k and info i to the WAVL tree. the tree must remain
	 * valid (keep its invariants). returns the number of rebalancing operations, or
	 * 0 if no rebalancing operations were necessary. returns -1 if an item with key
	 * k already exists in the tree.
	 */
	
	public int insert(int k, String i) {

		WAVLNode new_node = this.new WAVLNode(k, i);

		if (empty()) {
			this.root = new_node;
			min = root;
			max = root;
			return 0;
		}
		if (search(k) != null) {
			return -1;
		}
		//the method search updated pointer to be the place where we need to insert
		if (pointer.getKey() < k)
			pointer.setSon(new_node, Direction.Right);
		else
			pointer.setSon(new_node, Direction.Left);

		subTreeSizeUpdates(pointer, Action.Insert);
		int cnt = 0;

		if (pointer.rank == 0) {
			/// if it's a leaf we need to promote,
			// else no need to promote
			Promote(pointer);
			cnt += 1;
			cnt += RebalanceForInsert(pointer);
		}

		updateMinMax(new_node);

		return cnt;
	}

	
	// If the deleted node has a right son, we need to replace him by the successor.
	// This method change the pointers to perform this act.

	public void Swap(WAVLNode A, WAVLNode B, Case casee) {
		if (casee == Case.SpecialCase) {
			(B.getFather()).setSon(B.getRight(), Direction.Left);
			B.setSon(A.getSon(Direction.Right), Direction.Right);
		}
		if (casee == Case.HasRightSonCase) {
			B.setSon(A.getLeft(), Direction.Left);
			B.rank = A.getRank();
			B.setSon(B.rightNode, Direction.Right);
		}
	}
	
	
	/**
	 * public int delete(int k)
	 *
	 * deletes an item with key k from the binary tree, if it is there; the tree
	 * must remain valid (keep its invariants). returns the number of rebalancing
	 * operations, or 0 if no rebalancing operations were needed. returns -1 if an
	 * item with key k was not found in the tree.
	 */
	public int delete(int k) {
		//checks if the node exists in the tree.
		if (search(k) == null)
			return -1;
		// updates the minimum and the maximum if are deleted.
		if (pointer == min)
			replaceMin();
		if (pointer == max)
			replaceMax();

		WAVLNode father = pointer.getFather();
		Direction direction = Direction.Left;
		boolean HasRightSonCase = false, SpecialCase = false;
		WAVLNode SwapWith;
		WAVLNode nodeForSpecialCase = null;
		int cnt = 0;

		if (pointer!=root) {
			direction = WhichDirection(father, pointer);
		}
		//pointer need to be deleted
		if (pointer.isLeaf())  { 
			// deleting leaf
			subTreeSizeUpdates(pointer.father, Action.Delete);
			SwapWith = ext;
		}
		else {
			if (pointer.hasSon(Direction.Right) == false) {
				// deleting node who doesn't have right son
				SwapWith = pointer.getSon(Direction.Left);
				subTreeSizeUpdates(SwapWith.father, Action.Delete);
				}
			else { 
				// deleting node who has right son - replace him by it's successor
				HasRightSonCase = true;
				SwapWith = successor(pointer);
				SwapWith.subtreeSize = pointer.subtreeSize;
				subTreeSizeUpdates(SwapWith, Action.Delete);
				if (SwapWith.getFather() != pointer) {

//					the right son of the deleted node is not his successor:
//					 (d)
//						 \
//						 ()
//						 /
//					   ()
					
					SpecialCase = true;
					nodeForSpecialCase = SwapWith.rightNode;
					Swap(pointer, SwapWith, Case.SpecialCase);
				}
				Swap(pointer, SwapWith, Case.HasRightSonCase);
				cnt++; // swap changed rank
			}
		}

		if (pointer != root) {
			father.setSon(SwapWith, direction);
		}

		else {
			SwapWith.setFather(null);
			root = (SwapWith.isInnerNode()) ? SwapWith : null;
		}

		if (HasRightSonCase) { // if pointer replaced by its successor
			SwapWith = SwapWith.getSon(Direction.Right);
			if (SpecialCase) {
				SwapWith = nodeForSpecialCase;
			}
		}
		
		// item already deleted

		if (!empty() && SwapWith.father != null)
			// check if rebalance is needed
			cnt += RebalanceForDelete(SwapWith);

		return cnt;
	}
	
	
	// Rebalance the tree after insert
	// The method determines what action is needed to solve the ranks' problem: promote/Rotation/doubleRotation
	
	public int RebalanceForInsert(WAVLNode curr) {

		int cnt = 0;
		int dist;
		WAVLNode head, curr_son, grandfather;
		Direction direction;

		while (curr != root) {
			// we doesn't pass the root
			head = curr.father;
			if (head.rank == curr.rank) {
				// if there is a problem with the distance between the ranks of node and it's
				// parent
				direction = WhichDirection(head, curr);
				Direction opposite_direction = Direction.flip_direction(direction);
				dist = head.rank - head.getSon(opposite_direction).rank;
				curr_son = curr.getSon(direction);
					
				if (dist == 1) {
					Promote(head);
					cnt += 1;
					curr = curr.father;
				}
				if (dist == 2) {
					grandfather = head.father;
					if (curr.rank - curr_son.rank == 1) {
						cnt += Rotation(head, opposite_direction, Action.Insert);
						cnt += 1;
					} 
					else {
						curr = curr.getSon(opposite_direction);
						cnt += DoubleRotation(head, opposite_direction, Action.Insert);
						cnt += 2;
					}
					curr.fixFather(grandfather, head);
					break; // rotation and double_rotation are finite rebalancing operations
				}
			}

			else
				break;
		}
	return cnt;
	}

	public int RebalanceForDelete(WAVLNode son) {
		int cnt = 0;
		Direction direction;
		Direction opposite_direction;
		WAVLNode father, grandfather, other;
		int D1, D2, D3, D4; // distances after deletion
		boolean check;
		
		while (son != root) { // we don't pass the root
			father = son.getFather();
			direction = WhichDirection(father, son);
			opposite_direction = Direction.flip_direction(direction);
			other = father.getSon(opposite_direction);
			D1 = father.rank - son.rank;
			D2 = father.rank - other.rank;
			check = (D1 == 1 & D2 == 1) || (D1 == 2 & D2 == 2);
			 
			if ((father.rank == 1 & check)) {
				Demote(father);
				cnt++;
				son = son.getFather();
				continue;
			}
			
			if (father.rank - son.rank == 3) {
				if (D2 == 2) {
					Demote(father);
					cnt++;

				}
				if (D2 == 1) {
					son = other;
					direction = opposite_direction;
					opposite_direction = Direction.flip_direction(direction);
					D3 = son.rank - son.getSon(direction).rank;
					D4 = son.rank - son.getSon(opposite_direction).rank;
					grandfather = father.father;
				
					if (D3 == 1) {
						cnt += Rotation(father, opposite_direction, Action.Delete);
						cnt += 1;
						son.fixFather(grandfather, father);
						// Rotation is a finite action
						break;
					}
					else  { 
						if (D4 == 1) {
							son = son.getSon(opposite_direction);
							cnt += DoubleRotation(father, opposite_direction, Action.Delete);
							cnt += 2;
							son.fixFather(grandfather, father);
							// DoubleRotation is a finite action
							break;
						}
						if (D4 == 2) {
							DoubleDemote(father, son);
							cnt += 1;
						}
					}
				}
				son = son.getFather();
			}
			else
				// no problem with ranks
				break;
				
		}
		
		return cnt;	

		}
	

	public void Promote(WAVLNode node) {
		node.rank += 1;
	}
	
	public void Demote(WAVLNode node) {
		node.rank -= 1;
	}

	private void DoubleDemote(WAVLNode father, WAVLNode son) {
		Demote(father);
		Demote(son);
	}
	
	//check if it's a 2,2 node
	public boolean IsTwoTwoNode(WAVLNode node) {
		int rank1 = node.getSon(Direction.Left).getRank();
		int rank2 = node.getSon(Direction.Right).getRank();
		return (node.getRank() - rank1 == 2) && (node.getRank() - rank2 == 2);
	}
	
	
	public int Rotation(WAVLNode head,Direction direction, Action action) {      // gets head and to which direction to rotate
		int cnt = 0;
		Direction opposite_direction = Direction.flip_direction(direction);
		WAVLNode curr = head.getSon(opposite_direction);
		head.setSon(curr.getSon(direction), opposite_direction);
		curr.setSon(head, direction);
		Demote(head);
		cnt++;
		head.subtreeSize = head.subtreeSize - curr.getSon(opposite_direction).subtreeSize - 1; // remove x and add b
		curr.subtreeSize = curr.subtreeSize + head.getSon(direction).subtreeSize + 1;
		//next line fixs ranks
		if (action == Action.Delete || (action == Action.Insert & (curr.rank == head.rank))) {
			Promote(curr);
			cnt++;
		}
		if (IsTwoTwoNode(head) && action==Action.Delete) {
			Demote(head);
			cnt++;
		}
		return cnt;
	}
	
	// DoubleRotation uses Rotation twice
	public int DoubleRotation(WAVLNode head,Direction direction,Action action) {
		int cnt = 0;
		int rank = head.getRank();
		Direction opposite_direction = Direction.flip_direction(direction);
		WAVLNode curr = head.getSon(opposite_direction);
		WAVLNode other = curr.getSon(direction);
		cnt += Rotation(curr, opposite_direction, action);
		head.setSon(other, opposite_direction); // fix other's father pointer
		cnt += Rotation(head, direction, action);
		if (action == Action.Delete && (rank - head.getRank() != 2)) {
			Demote(head);
			cnt++;
		}
		return cnt;
	}
	
	// Get left as far as possible
	public WAVLNode localMin(WAVLNode node) {
		WAVLNode min = node;
		while (min.isInnerNode()) {
			if (!min.getLeft().isInnerNode())
				return min;
			min = min.getLeft();
		}
		return min;
	}

	// Get right as far as possible
	public WAVLNode localMax(WAVLNode node) {
		WAVLNode max = node;
		while (max.isInnerNode()) {
			if (!max.getRight().isInnerNode())
				return max;
			max = max.getRight();
		}
		return max;
	}
	
	// return the node's successor
	public WAVLNode successor(WAVLNode node) {
		if (node.getRight().rank != -1)
			return localMin(node.getRight());
		WAVLNode father;
		father = node.getFather();
		while (father != null && node == father.getRight()) {
			node = father;
			father = node.getFather();
		}
		return father;
	}
	
	// return the node's predecesor
	public WAVLNode predecesor(WAVLNode node) {
		if (node.getLeft().rank != -1)
			return localMax(node.getLeft());
		WAVLNode father;
		father = node.getFather();
		while (father != null && node == father.getLeft()) {
			node = father;
			father = node.getFather();
		}
		return father;		
	}
	
	/**
	 * public String min()
	 *
	 * Returns the info of the item with the smallest key in the tree, or null if
	 * the tree is empty
	 */
	public String min() {
		if (empty())
			return null;
		return min.getValue();
	}

	/**
	 * public String max()
	 *
	 * Returns the info of the item with the largest key in the tree, or null if the
	 * tree is empty
	 */
	public String max() {
		if (empty())
			return null;
		return max.getValue();
	}

	
	//insert uses this method to update new min/max
	public void updateMinMax(WAVLNode node) {  
		if (node.getKey() < min.getKey())
			min = node;
		if (node.getKey() > max.getKey())
			max = node;
	}

	
	//delete uses this method to update min to be it's successor 
	public void replaceMin() {      
			min = successor(min);
	}
	
	//delete uses this method to update max to be it's predecesor 
	public void replaceMax() {    
		max = predecesor(max);
		
	}
	

	/**
	 * public int[] keysToArray()
	 *
	 * Returns a sorted array which contains all keys in the tree, or an empty array
	 * if the tree is empty.
	 */
	public int[] keysToArray() {
		if (empty()) {
			int[] arr = new int[0];
			return arr;
		}
		int[] arr1 = new int[size()];
		int i = 0;
		InOrderKeys(root, arr1, i);
		return arr1;
	}

	/**
	 * public String[] infoToArray()
	 *
	 * Returns an array which contains all info in the tree, sorted by their
	 * respective keys, or an empty array if the tree is empty.
	 */
	public String[] infoToArray() {
		if (empty()) {
			String[] arr = new String[0];
			return arr;
		}
		String[] arr1 = new String[size()];
		int i = 0;
		InOrderValues(root, arr1, i);
		return arr1;
	}

	//fill an array with all the keys, in their native order
	public int InOrderKeys(WAVLNode root,int[] arr1,int i) {
		if (root.key != -1) {
			// first recursive call
			i = InOrderKeys(root.leftNode, arr1, i);
			arr1[i++] = root.getKey();
			// second recursive call
			i = InOrderKeys(root.rightNode, arr1, i);
		}
		return i;
	}
	
	//fill an array with all the values 
	public int InOrderValues(WAVLNode root,String[] arr1,int i) {
		if (root.key != -1) {
			// first recursive call
			i = InOrderValues(root.leftNode, arr1, i);
			arr1[i++] = root.getValue();
			// second recursive call
			i = InOrderValues(root.rightNode, arr1, i);
		}
		return i;
	}
	
	/**
	 * public int size()
	 *
	 * Returns the number of nodes in the tree.
	 *
	 */
	public int size() {
		if (empty())
			return 0;
		return root.getSubtreeSize();
	}

	/**
	 * public WAVLNode getRoot()
	 *
	 * Returns the root WAVL node, or null if the tree is empty
	 *
	 */
	public WAVLNode getRoot() {
		return root;
	}

	/**
	 * public int select(int i)
	 *
	 * Returns the value of the i'th smallest key (return -1 if tree is empty)
	 * Example 1: select(1) returns the value of the node with minimal key Example
	 * 2: select(size()) returns the value of the node with maximal key Example 3:
	 * select(2) returns the value 2nd smallest minimal node, i.e the value of the
	 * node minimal node's successor
	 *
	 */
	
	// call select(node,i) with the root as a parameter
	public String select(int i) {
		if (root == null || root.getSubtreeSize() < i)
			return null;
		return select(root, i - 1).getValue();
	}

	public WAVLNode select(WAVLNode node, int i) {
		int r = node.getLeft().getSubtreeSize();
		if (i == r)
			return node;
		if (i < r)
			return select(node.getLeft(), i);
		return select(node.getRight(), i - r - 1);
	}
	
	
	/**
	 * public class WAVLNode
	 */
	public class WAVLNode {
		public int rank, key, subtreeSize;
		public String value;
		public WAVLNode leftNode, rightNode, father;

		public WAVLNode(int key, String value) {
			this.key = key;
			this.value = value;
			subtreeSize = 1;
			this.leftNode = ext;
			this.rightNode = ext;
		}

		public int getKey() {
			return key;
		}

		public String getValue() {
			return value;
		}
		
		public WAVLNode getFather() {
			return father;
		}
		
		public void setFather(WAVLNode father) {
			this.father = father;
		}
		
		public int getRank() {
			return rank;
		}
		
		// check if after rotation the root of the sub tree is the root of the big tree
		// if does, update the node to be the root
		// else set his father to be his prev grandfather
		public void fixFather(WAVLNode grandfather , WAVLNode prev_father  ) {
			if (prev_father != root) {
				Direction direction = WhichDirection(grandfather, father);
				grandfather.setSon(this, direction);
			}
			else {
				this.setFather(null);
				root = this;
			}
		}
		

		public WAVLNode getSon(Direction direction) {
			if (direction==Direction.Left)
				return leftNode;
			else 
				return rightNode;
		}

		
		 // set node as head's son by given direction
		public void setSon(WAVLNode node, Direction direction) {   
			if (direction == Direction.Left)
				this.leftNode = node;
			else
				this.rightNode = node;
			node.setFather(this);
		}
		
		
		// checks if node has a son 
		public boolean hasSon(Direction direction) {  
			return getSon(direction).getKey() != -1 ;
		
		}
		public WAVLNode getLeft() {
			return getSon(Direction.Left);
		}

		public WAVLNode getRight() {
			return getSon(Direction.Right);
		}

		public boolean isInnerNode() {
			return (key != -1);
		}
		
		// check if the nodes' two sons are external nodes in order to decide if the node is a leaf
		public boolean isLeaf() {
			return (getLeft()==ext & getRight()==ext);
		}
		
		public int getSubtreeSize() {
			return subtreeSize;
		}

	}
	
	// External Node class. Extends from WAVLNode
	public class WAVLExtNode extends WAVLNode {
		public WAVLExtNode() {
			super(-1, null);
			this.rank = -1;
			this.subtreeSize = 0;
		}
	}
	
}