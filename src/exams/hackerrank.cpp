#include <bits/stdc++.h>

using namespace std;

string ltrim(const string &);
string rtrim(const string &);

class SinglyLinkedListNode {
    public:
        int data;
        SinglyLinkedListNode *next;

        SinglyLinkedListNode(int node_data) {
            this->data = node_data;
            this->next = nullptr;
        }
};
class SinglyLinkedList {
    public:
        SinglyLinkedListNode *head;
        SinglyLinkedListNode *tail;

        SinglyLinkedList() {
            this->head = nullptr;
            this->tail = nullptr;
        }

        void insert_node(int node_data) {
            SinglyLinkedListNode* node = new SinglyLinkedListNode(node_data);

            if (!this->head) {
                this->head = node;
            } else {
                this->tail->next = node;
            }

            this->tail = node;
        }
};

void print_singly_linked_list(SinglyLinkedListNode* node, string sep/*, ofstream& fout*/) {
    if (node != NULL) {
        print_singly_linked_list( node->next, sep);
        cout << node->data << sep;
    }
}
/*
 * Complete the 'getNumber' function below.
 *
 * The function is expected to return a LONG_INTEGER.
 * The function accepts INTEGER_SINGLY_LINKED_LIST binary as parameter.
 *
 *
 * 
 * For your reference:
 *
 * SinglyLinkedListNode {
 *     int data;
 *     SinglyLinkedListNode* next;
 * };
 *
 */

long getNumber(SinglyLinkedListNode* binary) {
    long val;
    bool neg;
    int count = 0;
    SinglyLinkedListNode* theNode;

    while (theNode != NULL) {

    }

    return 1;
}
//int main()

string ltrim(const string &);
string rtrim(const string &);
vector<string> split(const string &);



/*
 * Complete the 'findBeforeMatrix' function below.
 *
 * The function is expected to return a 2D_INTEGER_ARRAY.
 * The function accepts 2D_INTEGER_ARRAY after as parameter.
 */
vector<vector<int>> findBeforeMatrix(vector<vector<int>> after) {
    vector<vector<int>> before;
    int r_length = after.size(),
        c_length = after[0].size(),
        temp = 0;

    for (int i = 0; i < r_length; i++) {
        for (int j; j < c_length; j++) {
            if (i == 0 && j == 0)
                temp = after[0][0];
            else if (i == 0)
                temp = after[0][j] - after[0][j-1]; 
            else if (j == 0)
                temp = after[i][0] - after[i-1][0];
            else
                temp = after[i][j] + after[i-1][j-1] - after[i][j-1] - after[i-1][j];
        }
        before[i].push_back(temp);
    }

    return before;
}
/*
 * Complete the 'preprocessDate' function below.
 *
 * The function is expected to return a STRING_ARRAY.
 * The function accepts STRING_ARRAY dates as parameter.
 */
vector<string> preprocessDate(vector<string> dates) {
    return vector<string> { "foo", "bar" };
}
