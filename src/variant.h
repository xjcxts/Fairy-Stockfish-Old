/*
  Fairy-Stockfish, a UCI chess variant playing engine derived from Stockfish
  Copyright (C) 2018-2022 Fabian Fichter

  Fairy-Stockfish is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Fairy-Stockfish is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#ifndef VARIANT_H_INCLUDED
#define VARIANT_H_INCLUDED

#include <set>
#include <map>
#include <vector>
#include <string>
#include <functional>
#include <sstream>
#include <iostream>

#include "types.h"
#include "bitboard.h"

namespace Stockfish {

/// Variant struct stores information needed to determine the rules of a variant.

struct Variant {
  std::string variantTemplate = "fairy";
  std::string pieceToCharTable = "-";
  int pocketSize = 0;
  Rank maxRank = RANK_10;
  File maxFile = FILE_I;
  bool chess960 = false;
  bool twoBoards = false;
  int pieceValue[PHASE_NB][PIECE_TYPE_NB] = {};
  std::string customPiece[CUSTOM_PIECES_NB] = {};
  std::set<PieceType> pieceTypes = { PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING };
  std::string pieceToChar =  " PNBRQ" + std::string(KING - QUEEN - 1, ' ') + "K" + std::string(PIECE_TYPE_NB - KING - 1, ' ')
                           + " pnbrq" + std::string(KING - QUEEN - 1, ' ') + "k" + std::string(PIECE_TYPE_NB - KING - 1, ' ');
  std::string pieceToCharSynonyms = std::string(PIECE_NB, ' ');
  std::string startFen = "rnbakabnr/9/1c5c1/p1p1p1p1p/9/9/P1P1P1P1P/1C5C1/9/RNBAKABNR w - - 0 1";
  Bitboard mobilityRegion[COLOR_NB][PIECE_TYPE_NB] = {};
  Bitboard boardbb[COLOR_NB][PIECE_TYPE_NB] = {};
  Rank promotionRank = RANK_8;
  std::set<PieceType, std::greater<PieceType> > promotionPieceTypes = { QUEEN, ROOK, BISHOP, KNIGHT };
  bool sittuyinPromotion = false;
  int promotionLimit[PIECE_TYPE_NB] = {}; // 0 means unlimited
  PieceType promotedPieceType[PIECE_TYPE_NB] = {};
  bool piecePromotionOnCapture = false;
  bool mandatoryPawnPromotion = true;
  bool mandatoryPiecePromotion = false;
  bool pieceDemotion = false;
  bool blastOnCapture = false;
  bool doubleStep = true;
  Rank doubleStepRank = RANK_2;
  Rank doubleStepRankMin = RANK_2;
  Bitboard enPassantRegion = AllSquares;
  bool castling = true;
  bool castlingDroppedPiece = false;
  File castlingKingsideFile = FILE_G;
  File castlingQueensideFile = FILE_C;
  Rank castlingRank = RANK_1;
  File castlingKingFile = FILE_E;
  PieceType castlingKingPiece = KING;
  PieceType castlingRookPiece = ROOK;
  PieceType kingType = KING;
  bool checking = true;
  bool dropChecks = true;
  bool mustCapture = false;
  bool mustDrop = false;
  PieceType mustDropType = ALL_PIECES;
  bool pieceDrops = false;
  bool dropLoop = false;
  bool capturesToHand = false;
  bool firstRankPawnDrops = false;
  bool promotionZonePawnDrops = false;
  bool dropOnTop = false;
  EnclosingRule enclosingDrop = NO_ENCLOSING;
  Bitboard enclosingDropStart = 0;
  Bitboard whiteDropRegion = AllSquares;
  Bitboard blackDropRegion = AllSquares;
  bool sittuyinRookDrop = false;
  bool dropOppositeColoredBishop = false;
  bool dropPromoted = false;
  PieceType dropNoDoubled = NO_PIECE_TYPE;
  int dropNoDoubledCount = 1;
  bool immobilityIllegal = false;
  bool gating = false;
  bool arrowGating = false;
  bool cambodianMoves = false;
  Bitboard diagonalLines = 0;
  bool pass = false;
  bool passOnStalemate = false;
  Rank soldierPromotionRank = RANK_6;
  EnclosingRule flipEnclosedPieces = NO_ENCLOSING;
  bool freeDrops = false;

  // game end
  int nMoveRule = 50;
  int nFoldRule = 3;
  Value nFoldValue = VALUE_DRAW;
  bool nFoldValueAbsolute = false;
  bool perpetualCheckIllegal = true;
  bool moveRepetitionIllegal = false;
  ChasingRule chasingRule = NO_CHASING;
  Value stalemateValue = VALUE_DRAW;
  bool stalematePieceCount = false; // multiply stalemate value by sign(count(~stm) - count(stm))
  Value checkmateValue = -VALUE_MATE;
  Value extinctionValue = VALUE_NONE;
  bool extinctionClaim = false;
  bool extinctionPseudoRoyal = false;
  std::set<PieceType> extinctionPieceTypes = {};
  int extinctionPieceCount = 0;
  int extinctionOpponentPieceCount = 0;
  PieceType flagPiece = NO_PIECE_TYPE;
  Bitboard whiteFlag = 0;
  Bitboard blackFlag = 0;
  bool flagMove = false;
  int connectN = 0;
  MaterialCounting materialCounting = NO_MATERIAL_COUNTING;

  std::string nnueAlias = "";
  PieceType nnueKing = KING;
  int nnueDimensions;
  bool nnueUsePockets;
  int pieceSquareIndex[COLOR_NB][PIECE_NB];
  int pieceHandIndex[COLOR_NB][PIECE_NB];
  int kingSquareIndex[SQUARE_NB];
  int nnueMaxPieces;

  void add_piece(PieceType pt, char c, std::string betza = "", char c2 = ' ') {
      pieceToChar[make_piece(WHITE, pt)] = toupper(c);
      pieceToChar[make_piece(BLACK, pt)] = tolower(c);
      pieceToCharSynonyms[make_piece(WHITE, pt)] = toupper(c2);
      pieceToCharSynonyms[make_piece(BLACK, pt)] = tolower(c2);
      pieceTypes.insert(pt);
      // Add betza notation for custom piece
      if (is_custom(pt))
          customPiece[pt - CUSTOM_PIECES] = betza;
  }

  void add_piece(PieceType pt, char c, char c2) {
      add_piece(pt, c, "", c2);
  }

  void remove_piece(PieceType pt) {
      pieceToChar[make_piece(WHITE, pt)] = ' ';
      pieceToChar[make_piece(BLACK, pt)] = ' ';
      pieceToCharSynonyms[make_piece(WHITE, pt)] = ' ';
      pieceToCharSynonyms[make_piece(BLACK, pt)] = ' ';
      pieceTypes.erase(pt);
  }

  void reset_pieces() {
      pieceToChar = std::string(PIECE_NB, ' ');
      pieceToCharSynonyms = std::string(PIECE_NB, ' ');
      pieceTypes.clear();
  }

  // Reset values that always need to be redefined
  Variant* init() {
      nnueAlias = "";
      return this;
  }

  // Pre-calculate derived properties
  Variant* conclude() {

      // Initialize calculated NNUE properties
      nnueKing =  pieceTypes.find(KING) != pieceTypes.end() ? KING
                : extinctionPieceCount == 0 && extinctionPieceTypes.find(COMMONER) != extinctionPieceTypes.end() ? COMMONER
                : NO_PIECE_TYPE;
      if (nnueKing != NO_PIECE_TYPE)
      {
          std::string fenBoard = startFen.substr(0, startFen.find(' '));
          // Switch NNUE from KA to A if there is no unique piece
          if (   std::count(fenBoard.begin(), fenBoard.end(), pieceToChar[make_piece(WHITE, nnueKing)]) != 1
              || std::count(fenBoard.begin(), fenBoard.end(), pieceToChar[make_piece(BLACK, nnueKing)]) != 1)
              nnueKing = NO_PIECE_TYPE;
      }
      int nnueSquares = (RANK_10 + 1) * (FILE_I + 1);
      nnueUsePockets = false;
      int nnuePockets = 0;
      int nnueNonDropPieceIndices = (2 * pieceTypes.size() - (nnueKing != NO_PIECE_TYPE)) * nnueSquares;
      int nnuePieceIndices = nnueNonDropPieceIndices + 2 * (pieceTypes.size() - (nnueKing != NO_PIECE_TYPE)) * nnuePockets;
      int i = 0;
      for (PieceType pt : pieceTypes)
      {
          for (Color c : { WHITE, BLACK})
          {
              pieceSquareIndex[c][make_piece(c, pt)] = 2 * i * nnueSquares;
              pieceSquareIndex[c][make_piece(~c, pt)] = (2 * i + (pt != nnueKing)) * nnueSquares;
              pieceHandIndex[c][make_piece(c, pt)] = 2 * i * nnuePockets + nnueNonDropPieceIndices;
              pieceHandIndex[c][make_piece(~c, pt)] = (2 * i + 1) * nnuePockets + nnueNonDropPieceIndices;
          }
          i++;
      }

      // Map king squares to enumeration of actually available squares.
      // E.g., for xiangqi map from 0-89 to 0-8.
      // Variants might be initialized before bitboards, so do not rely on precomputed bitboards (like SquareBB).
      int nnueKingSquare = 0;
      if (nnueKing)
          for (Square s = SQ_A1; s < nnueSquares; ++s)
          {
              Square bitboardSquare = Square(s + s / (maxFile + 1) * (FILE_MAX - maxFile));
              if (   !mobilityRegion[WHITE][nnueKing] || !mobilityRegion[BLACK][nnueKing]
                  || (mobilityRegion[WHITE][nnueKing] & make_bitboard(bitboardSquare))
                  || (mobilityRegion[BLACK][nnueKing] & make_bitboard(relative_square(BLACK, bitboardSquare, RANK_10))))
              {
                  kingSquareIndex[s] = nnueKingSquare++ * nnuePieceIndices;
              }
          }
      else
          kingSquareIndex[SQ_A1] = nnueKingSquare++ * nnuePieceIndices;
      nnueDimensions = nnueKingSquare * nnuePieceIndices;

      // Determine maximum piece count
      std::istringstream ss(startFen);
      ss >> std::noskipws;
      unsigned char token;
      nnueMaxPieces = 0;
      while ((ss >> token) && !isspace(token))
      {
          if (pieceToChar.find(token) != std::string::npos || pieceToCharSynonyms.find(token) != std::string::npos)
              nnueMaxPieces++;
      }

      return this;
  }

  void late_init() {
      for (Color c : {WHITE, BLACK})
          for (int pt = 0; pt < PIECE_TYPE_NB; pt++) {
              auto board_bb = board_size_bb(maxFile, maxRank);
              boardbb[c][pt] = mobilityRegion[c][pt] ? mobilityRegion[c][pt] & board_bb : board_bb;
          }
  }
};

class VariantMap : public std::map<std::string, const Variant*> {
public:
  void init();
  template <bool DoCheck> void parse(std::string path);
  template <bool DoCheck> void parse_istream(std::istream& file);
  void clear_all();
  std::vector<std::string> get_keys();

private:
  void add(std::string s, Variant* v);
};

extern VariantMap variants;

} // namespace Stockfish

#endif // #ifndef VARIANT_H_INCLUDED
